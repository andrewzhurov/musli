//! Example showcases how a [DAG] can be encoded and accessed.
//!
//! This encodes the same DAG which is visible on the Wikipedia page linked, at
//! time of writing it looked like this:
//!
//! ```text
//! a → b
//! a → d
//! a → c
//! a → e
//! b → d
//! c → d
//! c → e
//! d → e
//! ```
//!
//! [DAG]: <https://en.wikipedia.org/wiki/Directed_acyclic_graph>)

use anyhow::{Context, Error};
use musli_zerocopy::{Buf, OwnedBuf, Ref, ZeroCopy};

#[derive(ZeroCopy)]
#[repr(C)]
struct Node {
    id: char,
    parents: Ref<[Ref<Node>]>,
}

fn store_dag(buf: &mut OwnedBuf) -> Ref<Node> {
    let a = buf.store_uninit::<Node>();
    let b = buf.store_uninit::<Node>();
    let c = buf.store_uninit::<Node>();
    let d = buf.store_uninit::<Node>();
    let e = buf.store_uninit::<Node>();

    let parents = buf.store_slice::<Ref<Node>>(&[]);
    buf.load_uninit_mut(e).write(&Node { id: 'e', parents });
    let e = e.assume_init();

    let parents = buf.store_slice(&[e]);
    buf.load_uninit_mut(d).write(&Node { id: 'd', parents });
    let d = d.assume_init();

    let parents = buf.store_slice(&[d, e]);
    buf.load_uninit_mut(c).write(&Node { id: 'c', parents });
    let c = c.assume_init();

    let parents = buf.store_slice(&[d]);
    buf.load_uninit_mut(b).write(&Node { id: 'b', parents });
    let b = b.assume_init();

    let parents = buf.store_slice(&[b, c, e]);
    buf.load_uninit_mut(a).write(&Node { id: 'a', parents });
    a.assume_init()
}

fn example_store_and_load_dag() -> Result<(), Error> {
    let mut buf = OwnedBuf::new();

    let a_ref = store_dag(&mut buf);

    let a = buf.load(a_ref)?;

    let b = buf.load(a.parents.get(0).context("missing node")?)?;
    let b = buf.load(*b)?;

    let d = buf.load(b.parents.get(0).context("missing node")?)?;
    let d = buf.load(*d)?;

    dbg!(a.id, a.parents.len());
    dbg!(b.id, b.parents.len());
    dbg!(d.id, d.parents.len());

    Ok(())
}

fn example_store_and_load_dag_bytes() -> Result<(), Error> {
    let mut buf_original = OwnedBuf::new();

    store_dag(&mut buf_original);

    let bytes = buf_original.as_slice();

    // say you send it over-the-wire,
    // the recipient then could read it as

    let buf = Buf::new(bytes);
    let a_ref = Ref::<Node>::zero();
    let a = buf.load(a_ref)?;
    let a_parent_refs = buf.load(a.parents)?;
    for a_parent_ref in a_parent_refs {
        let a_parent = buf.load(*a_parent_ref)?;
        dbg!(a.id, a_parent.id);
    }
    Ok(())
}

fn example_dag_depth_first_walk() -> Result<(), Error> {
    let mut buf_original = OwnedBuf::new();

    store_dag(&mut buf_original);

    let bytes = buf_original.as_slice();

    // say you send it over-the-wire,
    // recipient could walk the DAG as

    let buf = Buf::new(bytes);
    let on_node = |node: &Node| println!("On node: {}", node.id);
    depth_first_walk(buf, &on_node)?;

    Ok(())
}

/// An example helper function that performs depth-first traversal of a DAG from its root Node,
/// calling the supplied `on_node` with each visited node.
/// `buf` is expected to contain root Node.
fn depth_first_walk<'a, F: Fn(&'a Node)>(buf: &'a Buf, on_node: &'a F) -> Result<(), Error> {
    let root_node_ref = Ref::<Node>::zero();
    depth_first_walk_step(buf, on_node, root_node_ref)?;
    Ok(())
}

fn depth_first_walk_step<'a, F: Fn(&'a Node)>(
    buf: &'a Buf,
    on_node: &'a F,
    node_ref: Ref<Node>,
) -> Result<(), Error> {
    let node = buf.load(node_ref)?;
    on_node(node);
    let parent_refs = buf.load(node.parents)?;
    for parent_ref in parent_refs {
        depth_first_walk_step(buf, on_node, *parent_ref)?;
    }
    Ok(())
}

fn example_dag_depth_first_take_while() -> Result<(), Error> {
    let mut buf_original = OwnedBuf::new();

    let _root_ref = store_dag(&mut buf_original);

    let root_bytes = buf_original.as_slice();

    // say you send the DAG over over-the-wire,
    // but recipient already knows some sub-DAG of it,
    // then they could collect only novel nodes like so

    let known_node_ids = ['d', 'e'];
    let buf = Buf::new(root_bytes);
    let is_novel = |node: &Node| !known_node_ids.contains(&node.id);
    let novel_nodes = depth_first_take_while(buf, &is_novel)?;
    let novel_node_ids = novel_nodes.iter().map(|node| node.id).collect::<Vec<_>>();
    assert_eq!(novel_node_ids, vec!['b', 'c', 'a']);

    Ok(())
}

/// An example helper function that performs depth-first traversal of a DAG from its root Node,
/// taking nodes while the `pred` returns 'true', collecting into Vec<&Node>.
/// This allows to signal to short-curcuit further in-depth traversal by returning 'false'.
/// Sparing us the cost of validating the nodes below, as they're not touched.
/// Returned Vec<&Node> is in depth-first order, meaning the first visited leaf is first, the root is last.
/// `buf` is expected to contain root Node.
/// Returns Err only if failed to load a visited Node.
fn depth_first_take_while<'a, F: Fn(&'a Node) -> bool>(
    buf: &'a Buf,
    pred: &'a F,
) -> Result<Vec<&'a Node>, Error> {
    let root_node_ref = Ref::<Node>::zero();
    depth_first_take_while_step(buf, pred, root_node_ref)
}

fn depth_first_take_while_step<'a, F: Fn(&'a Node) -> bool>(
    buf: &'a Buf,
    pred: &'a F,
    node_ref: Ref<Node>,
) -> Result<Vec<&'a Node>, Error> {
    let node = buf.load(node_ref)?;
    let out = if !pred(node) {
        vec![]
    } else {
        let parent_refs = buf.load(node.parents)?;
        let mut out_acc = parent_refs
            .iter()
            .map(|parent_ref| depth_first_take_while_step(buf, pred, *parent_ref))
            // returns Err if any parent nodes return Err
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .flatten()
            .collect::<Vec<&Node>>();
        out_acc.push(node);
        out_acc
    };

    Ok(out)
}

fn main() -> Result<(), Error> {
    example_store_and_load_dag()?;
    example_store_and_load_dag_bytes()?;
    example_dag_depth_first_walk()?;
    example_dag_depth_first_take_while()?;

    Ok(())
}
