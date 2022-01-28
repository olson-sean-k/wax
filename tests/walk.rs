use build_fs_tree::{dir, file, Build, FileSystemTree};
use std::collections::HashSet;
use std::path::PathBuf;
use tempfile::{self, TempDir};

use wax::Glob;

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
    };
    let path = root.path().join("project");
    tree.build(&path).unwrap();
    (root, path)
}

#[test]
fn walk_with_tree() {
    let (_root, path) = temptree();

    let glob = Glob::new("**").unwrap();
    let paths: HashSet<_> = glob
        .walk(&path, usize::MAX)
        .flatten()
        .map(|entry| entry.into_path())
        .collect();
    assert_eq!(
        paths,
        IntoIterator::into_iter([
            path.join("doc"),
            path.join("doc/guide.md"),
            path.join("src"),
            path.join("src/glob.rs"),
            path.join("src/lib.rs"),
            path.join("tests"),
            path.join("tests/walk.rs"),
            path.join("README.md"),
        ])
        .collect(),
    );
}

#[test]
fn walk_with_invariant_terminating_component() {
    let (_root, path) = temptree();

    let glob = Glob::new("**/*.md").unwrap();
    let paths: HashSet<_> = glob
        .walk(&path, usize::MAX)
        .flatten()
        .map(|entry| entry.into_path())
        .collect();
    assert_eq!(
        paths,
        IntoIterator::into_iter([path.join("doc/guide.md"), path.join("README.md"),]).collect(),
    );
}

#[test]
fn walk_with_invariant_intermediate_component() {
    let (_root, path) = temptree();

    let glob = Glob::new("**/src/**/*.rs").unwrap();
    let paths: HashSet<_> = glob
        .walk(&path, usize::MAX)
        .flatten()
        .map(|entry| entry.into_path())
        .collect();
    assert_eq!(
        paths,
        IntoIterator::into_iter([path.join("src/glob.rs"), path.join("src/lib.rs"),]).collect(),
    );
}

#[test]
fn walk_with_invariant_glob() {
    let (_root, path) = temptree();

    let glob = Glob::new("src/lib.rs").unwrap();
    let paths: HashSet<_> = glob
        .walk(&path, usize::MAX)
        .flatten()
        .map(|entry| entry.into_path())
        .collect();
    assert_eq!(
        paths,
        IntoIterator::into_iter([path.join("src/lib.rs"),]).collect(),
    );
}

#[test]
fn walk_with_not() {
    let (_root, path) = temptree();

    let glob = Glob::new("**/*.{md,rs}").unwrap();
    let paths: HashSet<_> = glob
        .walk(&path, usize::MAX)
        .not(["**/tests/**"])
        .unwrap()
        .flatten()
        .map(|entry| entry.into_path())
        .collect();
    assert_eq!(
        paths,
        IntoIterator::into_iter([
            path.join("doc/guide.md"),
            path.join("src/glob.rs"),
            path.join("src/lib.rs"),
            path.join("README.md"),
        ])
        .collect(),
    );
}

// TODO: See `Glob::walk`.
//#[test]
//fn walk_with_exhausted_depth() {
//    let (_root, path) = temptree();
//
//    let glob = Glob::new("src/lib.rs").unwrap();
//    let paths: HashSet<_> = glob
//        .walk(&path, 1)
//        .flatten()
//        .map(|entry| entry.into_path())
//        .collect();
//    assert!(paths.is_empty());
//}
