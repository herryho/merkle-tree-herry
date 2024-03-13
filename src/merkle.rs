/*

Building a simple Merkle Tree

Exercise 1:
    Given a set of data D, construct a Merkle Tree.

Assume that D is a power of 2 (the binary tree is perfect).

Example input:
    D = [A1, A2, A3, A4]

Example output:

                               Root
                           ┌──────────┐
                           │    H7    │
                           │ H(H5|H6) │
                  ┌────────┴──────────┴──────────┐
                  │                              │
                  │                              │
             ┌────┴─────┐                  ┌─────┴────┐
             │    H5    │                  │    H6    │
             │ H(H1|H2) │                  │ H(H3|H4) │
             └─┬─────┬──┘                  └─┬──────┬─┘
               │     │                       │      │
     ┌─────────┴┐   ┌┴─────────┐    ┌────────┴─┐  ┌─┴────────┐
     │   H1     │   │    H2    │    │    H3    │  │    H4    │
     │  H(A1)   │   │   H(A2)  │    │   H(A3)  │  │   H(A4)  │
     └───┬──────┘   └────┬─────┘    └────┬─────┘  └────┬─────┘
         │               │               │             │
         A1              A2              A3            A4


Exercise 1b:
    Write a function that will verify a given set of data with a given root hash.

Exercise 2:
    Write a function that will use a proof like the one in Exercise 3 to verify that the proof is indeed correct.

Exercise 3 (Hard):
    Write a function that returns a proof that a given data is in the tree.

    Hints:
        -   The proof should be a set of ordered data hashes and their positions (left 0 or right 1).
        -   Let's say we are asked to prove that H3 (A3) is in this tree. We have the entire tree so we can traverse it and find H3.
            Then we only need to return the hashes that can be used to calculate with the hash of the given data to calculate the root hash.
            i.e Given a data H3, a proof [(1, H4), (0, H5)] and a root:
                H3|H4 => H6 => H5|H6 => H7 = root

*/
#![allow(dead_code)]
#![allow(unused_variables)]
use sha2::Digest;
use std::rc::Rc;

pub type Data = Vec<u8>;
pub type Hash = Vec<u8>;

// node struct
#[derive(Debug, PartialEq, Eq, Clone)]
struct Node {
    hash: Hash,
    left: Option<Rc<Node>>,
    right: Option<Rc<Node>>,
}

impl Node {
    fn new(hash: Hash) -> Self {
        Node {
            hash,
            left: None,
            right: None,
        }
    }

    // create a new leaf node
    fn leaf(data: &Data) -> Self {
        Node::new(hash_data(data))
    }

    // create a new branch node
    fn branch(left: &Rc<Node>, right: &Rc<Node>) -> Self {
        // Calculate the combined hash of these two child nodes
        let combined_hash = hash_concat(&left.hash, &right.hash);

        Node {
            hash: combined_hash,
            left: Some(Rc::clone(left)),
            right: Some(Rc::clone(right)),
        }
    }
}

#[derive(PartialEq, Debug)]
pub struct MerkleTree {
    root: Option<Rc<Node>>,
}

/// Which side to put Hash on when concatinating proof hashes
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum HashDirection {
    Left,
    Right,
}

#[derive(Debug, Default, PartialEq)]
pub struct Proof<'a> {
    /// The hashes to use when verifying the proof
    /// The first element of the tuple is which side the hash should be on when concatinating
    hashes: Vec<(HashDirection, &'a Hash)>,
}

impl MerkleTree {
    /// Gets root hash for this tree
    pub fn root(&self) -> Hash {
        // Check if the root node exists
        if let Some(ref root_node) = self.root {
            // If it does, return a clone of its hash
            root_node.hash.clone()
        } else {
            // If the root node does not exist (the tree is empty), return an empty hash
            vec![]
        }
    }

    /// Constructs a Merkle tree from given input data
    pub fn construct(input: &[Data]) -> MerkleTree {
        // if input is an empty slice, return a tree with an node with a hash of empty vector
        if input.is_empty() {
            let empty_node = Node::new(hash_data(&vec![]));
            let empty_node = Rc::new(empty_node);
            return MerkleTree {
                root: Some(empty_node),
            };
        }

        // Convert the input data into leaf nodes
        let mut nodes: Vec<Rc<Node>> = input.iter().map(Node::leaf).map(Rc::new).collect();

        // Starting from the bottom, merge leaf nodes pairwise until only one root node remains
        while nodes.len() > 1 {
            // Used to store the nodes of the next level
            let mut next_level = Vec::new();
            for chunk in nodes.chunks(2) {
                match chunk {
                    // If there is only one node, promote it to the next level directly
                    [left] => next_level.push(Rc::clone(left)),
                    [left, right] => {
                        let parent = Rc::new(Node::branch(&Rc::clone(left), &Rc::clone(right)));
                        next_level.push(parent);
                    }
                    _ => (),
                }
            }

            // Set 'nodes' to be the next level and continue merging
            nodes = next_level;
        }

        // The remaining node is the root node
        let root = nodes.pop();

        // Construct MerkleTree
        MerkleTree { root }
    }

    /// Verifies that the given input data produces the given root hash
    pub fn verify(input: &[Data], root_hash: &Hash) -> bool {
        let tree = MerkleTree::construct(input);
        &tree.root() == root_hash
    }

    /// Verifies that the given data and proof_path correctly produce the given root_hash
    pub fn verify_proof(data: &Data, proof: &Proof, root_hash: &Hash) -> bool {
        // Hash the data first
        let mut hash = hash_data(data);

        for (direction, sibling_hash) in &proof.hashes {
            // Concatenate the proof hash with the current hash based on the proof direction,
            // obtaining a new hash. Repeat this process until the proof is exhausted.
            hash = match direction {
                HashDirection::Left => hash_concat(sibling_hash, &hash),
                HashDirection::Right => hash_concat(&hash, sibling_hash),
            };
        }

        // Compare the final hash with the root hash
        hash == *root_hash
    }

    /// Returns a list of hashes that can be used to prove that the given data is in this tree
    pub fn prove(&self, data: &Data) -> Option<Proof> {
        let mut proof = Proof::default();
        let current_data_hash = hash_data(data);

        // If the tree is empty, return None immediately
        let mut current_node = self.root.as_ref()?;

        // Check if the root node is the only data point
        if current_node.left.is_none() && current_node.right.is_none() {
            return if current_node.hash == current_data_hash {
                // If the hash value of the root node matches the hash value of the data, return an empty proof
                Some(proof)
            } else {
                // If not matching, return None
                None
            };
        }

        // Store the hashes and directions along the path
        let mut path: Vec<(HashDirection, &Hash)> = Vec::new();

        // If the tree is not just a single node, start traversing
        while current_node.left.is_some() && current_node.right.is_some() {
            let left = current_node.left.as_ref().unwrap();
            let right = current_node.right.as_ref().unwrap();

            // Check if the direct hash values of the left and right nodes are equal to the hash value of the current data
            if left.hash == current_data_hash {
                path.push((HashDirection::Right, &right.hash));
                break;
            } else if right.hash == current_data_hash {
                path.push((HashDirection::Left, &left.hash));
                break;
            }

            // Check if the left node or the right node contains the hash value of the current data, and update the path and current node accordingly.
            if MerkleTree::contains_hash(left, &current_data_hash) {
                path.push((HashDirection::Right, &right.hash));
                current_node = left;
            } else if MerkleTree::contains_hash(right, &current_data_hash) {
                path.push((HashDirection::Left, &left.hash));
                current_node = right;
            } else {
                // If neither left nor right node contains the hash value of the current data, return None.
                return None;
            }
        }

        // Reverse the path to ensure that the proof is ordered from leaf nodes to the root node
        for &(direction, hash) in path.iter().rev() {
            proof.hashes.push((direction, hash));
        }

        Some(proof)
    }

    // Recursive call to check if the node contains the target hash
    fn contains_hash(node: &Node, target_hash: &Hash) -> bool {
        // Last layer node, compare the hash value directly
        if &node.hash == target_hash {
            return true;
        }

        // If it is not the last layer node, recursively call the left and right nodes
        if let Some(ref left) = node.left {
            if MerkleTree::contains_hash(left, target_hash) {
                return true;
            }
        }
        if let Some(ref right) = node.right {
            if MerkleTree::contains_hash(right, target_hash) {
                return true;
            }
        }

        // If neither the left nor the right node contains the target hash, return false
        false
    }
}

fn hash_data(data: &Data) -> Hash {
    sha2::Sha256::digest(data).to_vec()
}

fn hash_concat(h1: &Hash, h2: &Hash) -> Hash {
    let h3 = h1.iter().chain(h2).copied().collect();
    hash_data(&h3)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn example_data(n: usize) -> Vec<Data> {
        let mut data = vec![];
        for i in 0..n {
            data.push(vec![i as u8]);
        }
        data
    }

    #[test]
    fn test_constructions() {
        let data = example_data(4);
        let tree = MerkleTree::construct(&data);
        let expected_root = "9675e04b4ba9dc81b06e81731e2d21caa2c95557a85dcfa3fff70c9ff0f30b2e";
        assert_eq!(hex::encode(tree.root()), expected_root);

        // Uncomment if your implementation allows for unbalanced trees
        let data = example_data(3);
        let tree = MerkleTree::construct(&data);
        let expected_root = "773a93ac37ea78b3f14ac31872c83886b0a0f1fec562c4e848e023c889c2ce9f";
        assert_eq!(hex::encode(tree.root()), expected_root);

        let data = example_data(8);
        let tree = MerkleTree::construct(&data);
        let expected_root = "0727b310f87099c1ba2ec0ba408def82c308237c8577f0bdfd2643e9cc6b7578";
        assert_eq!(hex::encode(tree.root()), expected_root);
    }

    // Some edge cases
    #[test]
    fn test_empty_input_tree_construction() {
        let tree = MerkleTree::construct(&[]);

        let empty_input_node = Rc::new(Node::new(hash_data(&vec![])));
        let empty_input_merkle_tree = MerkleTree {
            root: Some(empty_input_node),
        };
        let empty_input_root_hash = hash_data(&vec![]);

        assert_eq!(&tree, &empty_input_merkle_tree);
        assert_eq!(tree.root(), empty_input_root_hash);
    }

    #[test]
    fn test_verify() {
        // balanced tree verification
        let data = example_data(4);
        let tree = MerkleTree::construct(&data);
        let root = tree.root();
        assert!(MerkleTree::verify(&data, &root));

        // unbalanced tree verification
        let data = example_data(3);
        let tree = MerkleTree::construct(&data);
        let root = tree.root();
        assert!(MerkleTree::verify(&data, &root));

        // empty input verification
        let data = vec![];
        let tree = MerkleTree::construct(&data);
        let root = tree.root();
        assert!(MerkleTree::verify(&data, &root));
    }

    #[test]
    fn test_verify_non_existent() {
        let data = example_data(4);
        let tree = MerkleTree::construct(&data);
        let root = tree.root();
        let five = vec![0x05];
        assert!(!MerkleTree::verify(&[five], &root));

        // empty tree verification
        // the tree root of empty input does not equal to tree root as None
        let tree = MerkleTree { root: None };
        let root = tree.root();
        assert!(!MerkleTree::verify(&[], &root));
    }

    #[test]
    fn test_verify_proof() {
        // balanced tree verification
        let data = example_data(4);
        let tree = MerkleTree::construct(&data);
        let root = tree.root();
        let proof = tree.prove(&data[2]).unwrap();
        assert!(MerkleTree::verify_proof(&data[2], &proof, &root));

        // unbalanced tree verification
        let data = example_data(3);
        let tree = MerkleTree::construct(&data);
        let root = tree.root();
        let proof = tree.prove(&data[2]).unwrap();
        assert!(MerkleTree::verify_proof(&data[2], &proof, &root));

        // empty input verification
        let tree = MerkleTree::construct(&[]);
        let root = tree.root();
        let proof = tree.prove(&[].to_vec()).unwrap();
        assert!(MerkleTree::verify_proof(&[].to_vec(), &proof, &root));
    }

    #[test]
    fn test_verify_proof_non_existent() {
        // non-empty tree verification
        let data1 = example_data(4);
        let tree1 = MerkleTree::construct(&data1);
        let proof1 = tree1.prove(&vec![0x01]).unwrap();

        let data2 = example_data(3);
        let tree2 = MerkleTree::construct(&data2);
        let root2 = tree2.root();
        assert!(!MerkleTree::verify_proof(&data1[2], &proof1, &root2));

        // empty tree verification
        let empty_tree = MerkleTree { root: None };
        let empty_root = empty_tree.root();

        // empty input tree does not equal to empty tree with root as None
        let empty_input_tree = MerkleTree::construct(&[]);
        let empty_input_proof = empty_input_tree.prove(&[].to_vec()).unwrap();
        assert!(!MerkleTree::verify_proof(
            &[].to_vec(),
            &empty_input_proof,
            &empty_root
        ));
    }

    #[test]
    fn test_prove() {
        // balanced tree verification
        let data = example_data(4);
        let tree = MerkleTree::construct(&data);
        let proof = tree.prove(&data[2]).unwrap();
        let root_hash = tree.root();
        assert!(MerkleTree::verify_proof(&data[2], &proof, &root_hash));

        // unbalanced tree verification
        let data = example_data(3);
        let tree = MerkleTree::construct(&data);
        let proof = tree.prove(&data[2]).unwrap();
        let root_hash = tree.root();
        assert!(MerkleTree::verify_proof(&data[2], &proof, &root_hash));

        // empty input verification
        let tree = MerkleTree::construct(&[]);
        let proof = tree.prove(&[].to_vec()).unwrap();
        let root_hash = tree.root();
        assert!(MerkleTree::verify_proof(&[].to_vec(), &proof, &root_hash));
    }

    #[test]
    fn test_prove_non_existent() {
        let data = example_data(4);
        let tree = MerkleTree::construct(&data);
        let proof = tree.prove(&vec![0x05]);
        assert_eq!(proof, None);

        // empty tree verification
        let tree = MerkleTree { root: None };
        let proof = tree.prove(&[].to_vec());
        assert_eq!(proof, None);
    }
}
