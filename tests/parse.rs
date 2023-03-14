use std::path::PathBuf;

use build_fs_tree::{FileSystemTree, dir};

use wax::{Glob};

use build_fs_tree::{file, Build};
use tempfile::{self, TempDir};


#[test]
fn test_parse_litteral(){
    let (_root, path) = temptree();

    test("README.md", &["README.md"], &path);
    test("tests/walk.rs", &["walk.rs"], &path);

    test("extra:dots.txt", &["extra:dots.txt"], &path);
    test("extra,comma.txt", &["extra,comma.txt"], &path);
}

#[test]
fn test_parse_wildcards(){
    let (_root, path) = temptree();

    test("RE*.md", &["README.md"], &path);
    test("READM?.md", &["README.md"], &path);
    test("**/*.md", &["guide.md", "README.md"], &path);

    test("*:dots.txt", &["extra:dots.txt"], &path);
    test("*,comma.txt", &["extra,comma.txt"], &path);
}

#[test]
fn test_parse_char_classes(){
    let (_root, path) = temptree();

    test("READM[AEIOU].md", &["README.md"], &path);
    test("READM[A-Z].md", &["README.md"], &path);
    test("READM[a-zA-Z].md", &["README.md"], &path);

    test("READM[!AIOU].md", &["README.md"], &path);

    test("extr[a-z]:dots.txt", &["extra:dots.txt"], &path);
    test("extr[a-z],comma.txt", &["extra,comma.txt"], &path);
}

#[test]
fn test_parse_alternatives(){
    let (_root, path) = temptree();

    test("READM{A,E}.md", &["README.md"], &path);
    test("READ{M?,Z?}.md", &["README.md"], &path);
    test("README.{txt,md}", &["README.md"], &path);

    test("extra{:dots,:nots}.txt", &["extra:dots.txt"], &path);
    test("extra{\\,comma,\\,nots}.txt", &["extra,comma.txt"], &path);
}

#[test]
fn test_parse_repetitions(){
    let (_root, path) = temptree();

    test("<t*/>walk.rs", &["walk.rs"], &path);
    test("<t*/:1>walk.rs", &["walk.rs"], &path);
    test("<t*/:0,1>walk.rs", &["walk.rs"], &path);
    test("fl<?:2>t.txt", &["fleet.txt"], &path);
    test("fl<e:2>t.txt", &["fleet.txt"], &path);

    test("extra:dots.txt", &["extra:dots.txt"], &path);
    test("extra,comma.txt", &["extra,comma.txt"], &path);
}

#[test]
fn test_parse_combined(){
    let (_root, path) = temptree();

    test("extra{[:,\\-]dots,:nots}.txt", &["extra:dots.txt"], &path);
}




fn test(expression: &str, expected: &[&str], path: &PathBuf){
    println!("\n\n\nTest {expression} {:?}", expected);
    let glob = Glob::new(expression).unwrap();
    println!("Captures: {:?}", glob.captures().collect::<Vec<_>>());
    println!("Glob: {:#?}", glob);

    let names: Vec<String> = glob.walk(path).filter_map(|e| {
        Some(e.unwrap().path().file_name().unwrap().to_string_lossy().to_string())
    }).collect();

    assert_eq!(expected, names);
}

// TODO: Rust's testing framework does not provide a mechanism for maintaining
//       shared state. This means that tests that write to the file system must
//       do so individually rather than writing before and after all tests have
//       run. This should probably be avoided.

/// Writes a testing directory tree to a temporary location on the file system.
fn temptree() -> (TempDir, PathBuf) {
    let root = tempfile::tempdir().unwrap();
    let tree: FileSystemTree<&str, &str> = dir! {
        "doc" => dir! {
            "guide.md" => file!(""),
        },
        "src" => dir! {
            "glob.rs" => file!(""),
            "lib.rs" => file!(""),
        },
        "tests" => dir! {
            "walk.rs" => file!(""),
        },
        "README.md" => file!(""),
        "fleet.txt" => file!(""),
        "extra:dots.txt" => file!(""),
        "extra,comma.txt" => file!(""),
    };
    let path = root.path().join("project");
    tree.build(&path).unwrap();
    (root, path)
}