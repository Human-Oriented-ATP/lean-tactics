const global = window;

import { jsxs, jsx } from 'react/jsx-runtime';
import * as React from 'react';
import React__default from 'react';
import require$$6 from 'react-dom';
import { GoalsLocation, LocationsContext, InteractiveCode } from '@leanprover/infoview';

/******************************************************************************
Copyright (c) Microsoft Corporation.

Permission to use, copy, modify, and/or distribute this software for any
purpose with or without fee is hereby granted.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES WITH
REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY
AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT,
INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM
LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR
OTHER TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR
PERFORMANCE OF THIS SOFTWARE.
***************************************************************************** */

var __assign = function() {
    __assign = Object.assign || function __assign(t) {
        for (var s, i = 1, n = arguments.length; i < n; i++) {
            s = arguments[i];
            for (var p in s) if (Object.prototype.hasOwnProperty.call(s, p)) t[p] = s[p];
        }
        return t;
    };
    return __assign.apply(this, arguments);
};

typeof SuppressedError === "function" ? SuppressedError : function (error, suppressed, message) {
    var e = new Error(message);
    return e.name = "SuppressedError", e.error = error, e.suppressed = suppressed, e;
};

function count(node) {
  var sum = 0,
      children = node.children,
      i = children && children.length;
  if (!i) sum = 1;
  else while (--i >= 0) sum += children[i].value;
  node.value = sum;
}

function node_count() {
  return this.eachAfter(count);
}

function node_each(callback) {
  var node = this, current, next = [node], children, i, n;
  do {
    current = next.reverse(), next = [];
    while (node = current.pop()) {
      callback(node), children = node.children;
      if (children) for (i = 0, n = children.length; i < n; ++i) {
        next.push(children[i]);
      }
    }
  } while (next.length);
  return this;
}

function node_eachBefore(callback) {
  var node = this, nodes = [node], children, i;
  while (node = nodes.pop()) {
    callback(node), children = node.children;
    if (children) for (i = children.length - 1; i >= 0; --i) {
      nodes.push(children[i]);
    }
  }
  return this;
}

function node_eachAfter(callback) {
  var node = this, nodes = [node], next = [], children, i, n;
  while (node = nodes.pop()) {
    next.push(node), children = node.children;
    if (children) for (i = 0, n = children.length; i < n; ++i) {
      nodes.push(children[i]);
    }
  }
  while (node = next.pop()) {
    callback(node);
  }
  return this;
}

function node_sum(value) {
  return this.eachAfter(function(node) {
    var sum = +value(node.data) || 0,
        children = node.children,
        i = children && children.length;
    while (--i >= 0) sum += children[i].value;
    node.value = sum;
  });
}

function node_sort(compare) {
  return this.eachBefore(function(node) {
    if (node.children) {
      node.children.sort(compare);
    }
  });
}

function node_path(end) {
  var start = this,
      ancestor = leastCommonAncestor(start, end),
      nodes = [start];
  while (start !== ancestor) {
    start = start.parent;
    nodes.push(start);
  }
  var k = nodes.length;
  while (end !== ancestor) {
    nodes.splice(k, 0, end);
    end = end.parent;
  }
  return nodes;
}

function leastCommonAncestor(a, b) {
  if (a === b) return a;
  var aNodes = a.ancestors(),
      bNodes = b.ancestors(),
      c = null;
  a = aNodes.pop();
  b = bNodes.pop();
  while (a === b) {
    c = a;
    a = aNodes.pop();
    b = bNodes.pop();
  }
  return c;
}

function node_ancestors() {
  var node = this, nodes = [node];
  while (node = node.parent) {
    nodes.push(node);
  }
  return nodes;
}

function node_descendants() {
  var nodes = [];
  this.each(function(node) {
    nodes.push(node);
  });
  return nodes;
}

function node_leaves() {
  var leaves = [];
  this.eachBefore(function(node) {
    if (!node.children) {
      leaves.push(node);
    }
  });
  return leaves;
}

function node_links() {
  var root = this, links = [];
  root.each(function(node) {
    if (node !== root) { // Don’t include the root’s parent, if any.
      links.push({source: node.parent, target: node});
    }
  });
  return links;
}

function hierarchy(data, children) {
  var root = new Node$1(data),
      valued = +data.value && (root.value = data.value),
      node,
      nodes = [root],
      child,
      childs,
      i,
      n;

  if (children == null) children = defaultChildren;

  while (node = nodes.pop()) {
    if (valued) node.value = +node.data.value;
    if ((childs = children(node.data)) && (n = childs.length)) {
      node.children = new Array(n);
      for (i = n - 1; i >= 0; --i) {
        nodes.push(child = node.children[i] = new Node$1(childs[i]));
        child.parent = node;
        child.depth = node.depth + 1;
      }
    }
  }

  return root.eachBefore(computeHeight);
}

function node_copy() {
  return hierarchy(this).eachBefore(copyData);
}

function defaultChildren(d) {
  return d.children;
}

function copyData(node) {
  node.data = node.data.data;
}

function computeHeight(node) {
  var height = 0;
  do node.height = height;
  while ((node = node.parent) && (node.height < ++height));
}

function Node$1(data) {
  this.data = data;
  this.depth =
  this.height = 0;
  this.parent = null;
}

Node$1.prototype = hierarchy.prototype = {
  constructor: Node$1,
  count: node_count,
  each: node_each,
  eachAfter: node_eachAfter,
  eachBefore: node_eachBefore,
  sum: node_sum,
  sort: node_sort,
  path: node_path,
  ancestors: node_ancestors,
  descendants: node_descendants,
  leaves: node_leaves,
  links: node_links,
  copy: node_copy
};

function defaultSeparation(a, b) {
  return a.parent === b.parent ? 1 : 2;
}

// function radialSeparation(a, b) {
//   return (a.parent === b.parent ? 1 : 2) / a.depth;
// }

// This function is used to traverse the left contour of a subtree (or
// subforest). It returns the successor of v on this contour. This successor is
// either given by the leftmost child of v or by the thread of v. The function
// returns null if and only if v is on the highest level of its subtree.
function nextLeft(v) {
  var children = v.children;
  return children ? children[0] : v.t;
}

// This function works analogously to nextLeft.
function nextRight(v) {
  var children = v.children;
  return children ? children[children.length - 1] : v.t;
}

// Shifts the current subtree rooted at w+. This is done by increasing
// prelim(w+) and mod(w+) by shift.
function moveSubtree(wm, wp, shift) {
  var change = shift / (wp.i - wm.i);
  wp.c -= change;
  wp.s += shift;
  wm.c += change;
  wp.z += shift;
  wp.m += shift;
}

// All other shifts, applied to the smaller subtrees between w- and w+, are
// performed by this function. To prepare the shifts, we have to adjust
// change(w+), shift(w+), and change(w-).
function executeShifts(v) {
  var shift = 0,
      change = 0,
      children = v.children,
      i = children.length,
      w;
  while (--i >= 0) {
    w = children[i];
    w.z += shift;
    w.m += shift;
    shift += w.s + (change += w.c);
  }
}

// If vi-’s ancestor is a sibling of v, returns vi-’s ancestor. Otherwise,
// returns the specified (default) ancestor.
function nextAncestor(vim, v, ancestor) {
  return vim.a.parent === v.parent ? vim.a : ancestor;
}

function TreeNode(node, i) {
  this._ = node;
  this.parent = null;
  this.children = null;
  this.A = null; // default ancestor
  this.a = this; // ancestor
  this.z = 0; // prelim
  this.m = 0; // mod
  this.c = 0; // change
  this.s = 0; // shift
  this.t = null; // thread
  this.i = i; // number
}

TreeNode.prototype = Object.create(Node$1.prototype);

function treeRoot(root) {
  var tree = new TreeNode(root, 0),
      node,
      nodes = [tree],
      child,
      children,
      i,
      n;

  while (node = nodes.pop()) {
    if (children = node._.children) {
      node.children = new Array(n = children.length);
      for (i = n - 1; i >= 0; --i) {
        nodes.push(child = node.children[i] = new TreeNode(children[i], i));
        child.parent = node;
      }
    }
  }

  (tree.parent = new TreeNode(null, 0)).children = [tree];
  return tree;
}

// Node-link tree diagram using the Reingold-Tilford "tidy" algorithm
function d3tree() {
  var separation = defaultSeparation,
      dx = 1,
      dy = 1,
      nodeSize = null;

  function tree(root) {
    var t = treeRoot(root);

    // Compute the layout using Buchheim et al.’s algorithm.
    t.eachAfter(firstWalk), t.parent.m = -t.z;
    t.eachBefore(secondWalk);

    // If a fixed node size is specified, scale x and y.
    if (nodeSize) root.eachBefore(sizeNode);

    // If a fixed tree size is specified, scale x and y based on the extent.
    // Compute the left-most, right-most, and depth-most nodes for extents.
    else {
      var left = root,
          right = root,
          bottom = root;
      root.eachBefore(function(node) {
        if (node.x < left.x) left = node;
        if (node.x > right.x) right = node;
        if (node.depth > bottom.depth) bottom = node;
      });
      var s = left === right ? 1 : separation(left, right) / 2,
          tx = s - left.x,
          kx = dx / (right.x + s + tx),
          ky = dy / (bottom.depth || 1);
      root.eachBefore(function(node) {
        node.x = (node.x + tx) * kx;
        node.y = node.depth * ky;
      });
    }

    return root;
  }

  // Computes a preliminary x-coordinate for v. Before that, FIRST WALK is
  // applied recursively to the children of v, as well as the function
  // APPORTION. After spacing out the children by calling EXECUTE SHIFTS, the
  // node v is placed to the midpoint of its outermost children.
  function firstWalk(v) {
    var children = v.children,
        siblings = v.parent.children,
        w = v.i ? siblings[v.i - 1] : null;
    if (children) {
      executeShifts(v);
      var midpoint = (children[0].z + children[children.length - 1].z) / 2;
      if (w) {
        v.z = w.z + separation(v._, w._);
        v.m = v.z - midpoint;
      } else {
        v.z = midpoint;
      }
    } else if (w) {
      v.z = w.z + separation(v._, w._);
    }
    v.parent.A = apportion(v, w, v.parent.A || siblings[0]);
  }

  // Computes all real x-coordinates by summing up the modifiers recursively.
  function secondWalk(v) {
    v._.x = v.z + v.parent.m;
    v.m += v.parent.m;
  }

  // The core of the algorithm. Here, a new subtree is combined with the
  // previous subtrees. Threads are used to traverse the inside and outside
  // contours of the left and right subtree up to the highest common level. The
  // vertices used for the traversals are vi+, vi-, vo-, and vo+, where the
  // superscript o means outside and i means inside, the subscript - means left
  // subtree and + means right subtree. For summing up the modifiers along the
  // contour, we use respective variables si+, si-, so-, and so+. Whenever two
  // nodes of the inside contours conflict, we compute the left one of the
  // greatest uncommon ancestors using the function ANCESTOR and call MOVE
  // SUBTREE to shift the subtree and prepare the shifts of smaller subtrees.
  // Finally, we add a new thread (if necessary).
  function apportion(v, w, ancestor) {
    if (w) {
      var vip = v,
          vop = v,
          vim = w,
          vom = vip.parent.children[0],
          sip = vip.m,
          sop = vop.m,
          sim = vim.m,
          som = vom.m,
          shift;
      while (vim = nextRight(vim), vip = nextLeft(vip), vim && vip) {
        vom = nextLeft(vom);
        vop = nextRight(vop);
        vop.a = v;
        shift = vim.z + sim - vip.z - sip + separation(vim._, vip._);
        if (shift > 0) {
          moveSubtree(nextAncestor(vim, v, ancestor), v, shift);
          sip += shift;
          sop += shift;
        }
        sim += vim.m;
        sip += vip.m;
        som += vom.m;
        sop += vop.m;
      }
      if (vim && !nextRight(vop)) {
        vop.t = vim;
        vop.m += sim - sop;
      }
      if (vip && !nextLeft(vom)) {
        vom.t = vip;
        vom.m += sip - som;
        ancestor = v;
      }
    }
    return ancestor;
  }

  function sizeNode(node) {
    node.x *= dx;
    node.y = node.depth * dy;
  }

  tree.separation = function(x) {
    return arguments.length ? (separation = x, tree) : separation;
  };

  tree.size = function(x) {
    return arguments.length ? (nodeSize = false, dx = +x[0], dy = +x[1], tree) : (nodeSize ? null : [dx, dy]);
  };

  tree.nodeSize = function(x) {
    return arguments.length ? (nodeSize = true, dx = +x[0], dy = +x[1], tree) : (nodeSize ? [dx, dy] : null);
  };

  return tree;
}

var xhtml = "http://www.w3.org/1999/xhtml";

var namespaces = {
  svg: "http://www.w3.org/2000/svg",
  xhtml: xhtml,
  xlink: "http://www.w3.org/1999/xlink",
  xml: "http://www.w3.org/XML/1998/namespace",
  xmlns: "http://www.w3.org/2000/xmlns/"
};

function namespace(name) {
  var prefix = name += "", i = prefix.indexOf(":");
  if (i >= 0 && (prefix = name.slice(0, i)) !== "xmlns") name = name.slice(i + 1);
  return namespaces.hasOwnProperty(prefix) ? {space: namespaces[prefix], local: name} : name; // eslint-disable-line no-prototype-builtins
}

function creatorInherit(name) {
  return function() {
    var document = this.ownerDocument,
        uri = this.namespaceURI;
    return uri === xhtml && document.documentElement.namespaceURI === xhtml
        ? document.createElement(name)
        : document.createElementNS(uri, name);
  };
}

function creatorFixed(fullname) {
  return function() {
    return this.ownerDocument.createElementNS(fullname.space, fullname.local);
  };
}

function creator(name) {
  var fullname = namespace(name);
  return (fullname.local
      ? creatorFixed
      : creatorInherit)(fullname);
}

function none() {}

function selector(selector) {
  return selector == null ? none : function() {
    return this.querySelector(selector);
  };
}

function selection_select(select) {
  if (typeof select !== "function") select = selector(select);

  for (var groups = this._groups, m = groups.length, subgroups = new Array(m), j = 0; j < m; ++j) {
    for (var group = groups[j], n = group.length, subgroup = subgroups[j] = new Array(n), node, subnode, i = 0; i < n; ++i) {
      if ((node = group[i]) && (subnode = select.call(node, node.__data__, i, group))) {
        if ("__data__" in node) subnode.__data__ = node.__data__;
        subgroup[i] = subnode;
      }
    }
  }

  return new Selection$1(subgroups, this._parents);
}

// Given something array like (or null), returns something that is strictly an
// array. This is used to ensure that array-like objects passed to d3.selectAll
// or selection.selectAll are converted into proper arrays when creating a
// selection; we don’t ever want to create a selection backed by a live
// HTMLCollection or NodeList. However, note that selection.selectAll will use a
// static NodeList as a group, since it safely derived from querySelectorAll.
function array(x) {
  return x == null ? [] : Array.isArray(x) ? x : Array.from(x);
}

function empty() {
  return [];
}

function selectorAll(selector) {
  return selector == null ? empty : function() {
    return this.querySelectorAll(selector);
  };
}

function arrayAll(select) {
  return function() {
    return array(select.apply(this, arguments));
  };
}

function selection_selectAll(select) {
  if (typeof select === "function") select = arrayAll(select);
  else select = selectorAll(select);

  for (var groups = this._groups, m = groups.length, subgroups = [], parents = [], j = 0; j < m; ++j) {
    for (var group = groups[j], n = group.length, node, i = 0; i < n; ++i) {
      if (node = group[i]) {
        subgroups.push(select.call(node, node.__data__, i, group));
        parents.push(node);
      }
    }
  }

  return new Selection$1(subgroups, parents);
}

function matcher(selector) {
  return function() {
    return this.matches(selector);
  };
}

function childMatcher(selector) {
  return function(node) {
    return node.matches(selector);
  };
}

var find = Array.prototype.find;

function childFind(match) {
  return function() {
    return find.call(this.children, match);
  };
}

function childFirst() {
  return this.firstElementChild;
}

function selection_selectChild(match) {
  return this.select(match == null ? childFirst
      : childFind(typeof match === "function" ? match : childMatcher(match)));
}

var filter = Array.prototype.filter;

function children() {
  return Array.from(this.children);
}

function childrenFilter(match) {
  return function() {
    return filter.call(this.children, match);
  };
}

function selection_selectChildren(match) {
  return this.selectAll(match == null ? children
      : childrenFilter(typeof match === "function" ? match : childMatcher(match)));
}

function selection_filter(match) {
  if (typeof match !== "function") match = matcher(match);

  for (var groups = this._groups, m = groups.length, subgroups = new Array(m), j = 0; j < m; ++j) {
    for (var group = groups[j], n = group.length, subgroup = subgroups[j] = [], node, i = 0; i < n; ++i) {
      if ((node = group[i]) && match.call(node, node.__data__, i, group)) {
        subgroup.push(node);
      }
    }
  }

  return new Selection$1(subgroups, this._parents);
}

function sparse(update) {
  return new Array(update.length);
}

function selection_enter() {
  return new Selection$1(this._enter || this._groups.map(sparse), this._parents);
}

function EnterNode(parent, datum) {
  this.ownerDocument = parent.ownerDocument;
  this.namespaceURI = parent.namespaceURI;
  this._next = null;
  this._parent = parent;
  this.__data__ = datum;
}

EnterNode.prototype = {
  constructor: EnterNode,
  appendChild: function(child) { return this._parent.insertBefore(child, this._next); },
  insertBefore: function(child, next) { return this._parent.insertBefore(child, next); },
  querySelector: function(selector) { return this._parent.querySelector(selector); },
  querySelectorAll: function(selector) { return this._parent.querySelectorAll(selector); }
};

function constant$3(x) {
  return function() {
    return x;
  };
}

function bindIndex(parent, group, enter, update, exit, data) {
  var i = 0,
      node,
      groupLength = group.length,
      dataLength = data.length;

  // Put any non-null nodes that fit into update.
  // Put any null nodes into enter.
  // Put any remaining data into enter.
  for (; i < dataLength; ++i) {
    if (node = group[i]) {
      node.__data__ = data[i];
      update[i] = node;
    } else {
      enter[i] = new EnterNode(parent, data[i]);
    }
  }

  // Put any non-null nodes that don’t fit into exit.
  for (; i < groupLength; ++i) {
    if (node = group[i]) {
      exit[i] = node;
    }
  }
}

function bindKey(parent, group, enter, update, exit, data, key) {
  var i,
      node,
      nodeByKeyValue = new Map,
      groupLength = group.length,
      dataLength = data.length,
      keyValues = new Array(groupLength),
      keyValue;

  // Compute the key for each node.
  // If multiple nodes have the same key, the duplicates are added to exit.
  for (i = 0; i < groupLength; ++i) {
    if (node = group[i]) {
      keyValues[i] = keyValue = key.call(node, node.__data__, i, group) + "";
      if (nodeByKeyValue.has(keyValue)) {
        exit[i] = node;
      } else {
        nodeByKeyValue.set(keyValue, node);
      }
    }
  }

  // Compute the key for each datum.
  // If there a node associated with this key, join and add it to update.
  // If there is not (or the key is a duplicate), add it to enter.
  for (i = 0; i < dataLength; ++i) {
    keyValue = key.call(parent, data[i], i, data) + "";
    if (node = nodeByKeyValue.get(keyValue)) {
      update[i] = node;
      node.__data__ = data[i];
      nodeByKeyValue.delete(keyValue);
    } else {
      enter[i] = new EnterNode(parent, data[i]);
    }
  }

  // Add any remaining nodes that were not bound to data to exit.
  for (i = 0; i < groupLength; ++i) {
    if ((node = group[i]) && (nodeByKeyValue.get(keyValues[i]) === node)) {
      exit[i] = node;
    }
  }
}

function datum(node) {
  return node.__data__;
}

function selection_data(value, key) {
  if (!arguments.length) return Array.from(this, datum);

  var bind = key ? bindKey : bindIndex,
      parents = this._parents,
      groups = this._groups;

  if (typeof value !== "function") value = constant$3(value);

  for (var m = groups.length, update = new Array(m), enter = new Array(m), exit = new Array(m), j = 0; j < m; ++j) {
    var parent = parents[j],
        group = groups[j],
        groupLength = group.length,
        data = arraylike(value.call(parent, parent && parent.__data__, j, parents)),
        dataLength = data.length,
        enterGroup = enter[j] = new Array(dataLength),
        updateGroup = update[j] = new Array(dataLength),
        exitGroup = exit[j] = new Array(groupLength);

    bind(parent, group, enterGroup, updateGroup, exitGroup, data, key);

    // Now connect the enter nodes to their following update node, such that
    // appendChild can insert the materialized enter node before this node,
    // rather than at the end of the parent node.
    for (var i0 = 0, i1 = 0, previous, next; i0 < dataLength; ++i0) {
      if (previous = enterGroup[i0]) {
        if (i0 >= i1) i1 = i0 + 1;
        while (!(next = updateGroup[i1]) && ++i1 < dataLength);
        previous._next = next || null;
      }
    }
  }

  update = new Selection$1(update, parents);
  update._enter = enter;
  update._exit = exit;
  return update;
}

// Given some data, this returns an array-like view of it: an object that
// exposes a length property and allows numeric indexing. Note that unlike
// selectAll, this isn’t worried about “live” collections because the resulting
// array will only be used briefly while data is being bound. (It is possible to
// cause the data to change while iterating by using a key function, but please
// don’t; we’d rather avoid a gratuitous copy.)
function arraylike(data) {
  return typeof data === "object" && "length" in data
    ? data // Array, TypedArray, NodeList, array-like
    : Array.from(data); // Map, Set, iterable, string, or anything else
}

function selection_exit() {
  return new Selection$1(this._exit || this._groups.map(sparse), this._parents);
}

function selection_join(onenter, onupdate, onexit) {
  var enter = this.enter(), update = this, exit = this.exit();
  if (typeof onenter === "function") {
    enter = onenter(enter);
    if (enter) enter = enter.selection();
  } else {
    enter = enter.append(onenter + "");
  }
  if (onupdate != null) {
    update = onupdate(update);
    if (update) update = update.selection();
  }
  if (onexit == null) exit.remove(); else onexit(exit);
  return enter && update ? enter.merge(update).order() : update;
}

function selection_merge(context) {
  var selection = context.selection ? context.selection() : context;

  for (var groups0 = this._groups, groups1 = selection._groups, m0 = groups0.length, m1 = groups1.length, m = Math.min(m0, m1), merges = new Array(m0), j = 0; j < m; ++j) {
    for (var group0 = groups0[j], group1 = groups1[j], n = group0.length, merge = merges[j] = new Array(n), node, i = 0; i < n; ++i) {
      if (node = group0[i] || group1[i]) {
        merge[i] = node;
      }
    }
  }

  for (; j < m0; ++j) {
    merges[j] = groups0[j];
  }

  return new Selection$1(merges, this._parents);
}

function selection_order() {

  for (var groups = this._groups, j = -1, m = groups.length; ++j < m;) {
    for (var group = groups[j], i = group.length - 1, next = group[i], node; --i >= 0;) {
      if (node = group[i]) {
        if (next && node.compareDocumentPosition(next) ^ 4) next.parentNode.insertBefore(node, next);
        next = node;
      }
    }
  }

  return this;
}

function selection_sort(compare) {
  if (!compare) compare = ascending;

  function compareNode(a, b) {
    return a && b ? compare(a.__data__, b.__data__) : !a - !b;
  }

  for (var groups = this._groups, m = groups.length, sortgroups = new Array(m), j = 0; j < m; ++j) {
    for (var group = groups[j], n = group.length, sortgroup = sortgroups[j] = new Array(n), node, i = 0; i < n; ++i) {
      if (node = group[i]) {
        sortgroup[i] = node;
      }
    }
    sortgroup.sort(compareNode);
  }

  return new Selection$1(sortgroups, this._parents).order();
}

function ascending(a, b) {
  return a < b ? -1 : a > b ? 1 : a >= b ? 0 : NaN;
}

function selection_call() {
  var callback = arguments[0];
  arguments[0] = this;
  callback.apply(null, arguments);
  return this;
}

function selection_nodes() {
  return Array.from(this);
}

function selection_node() {

  for (var groups = this._groups, j = 0, m = groups.length; j < m; ++j) {
    for (var group = groups[j], i = 0, n = group.length; i < n; ++i) {
      var node = group[i];
      if (node) return node;
    }
  }

  return null;
}

function selection_size() {
  let size = 0;
  for (const node of this) ++size; // eslint-disable-line no-unused-vars
  return size;
}

function selection_empty() {
  return !this.node();
}

function selection_each(callback) {

  for (var groups = this._groups, j = 0, m = groups.length; j < m; ++j) {
    for (var group = groups[j], i = 0, n = group.length, node; i < n; ++i) {
      if (node = group[i]) callback.call(node, node.__data__, i, group);
    }
  }

  return this;
}

function attrRemove$1(name) {
  return function() {
    this.removeAttribute(name);
  };
}

function attrRemoveNS$1(fullname) {
  return function() {
    this.removeAttributeNS(fullname.space, fullname.local);
  };
}

function attrConstant$1(name, value) {
  return function() {
    this.setAttribute(name, value);
  };
}

function attrConstantNS$1(fullname, value) {
  return function() {
    this.setAttributeNS(fullname.space, fullname.local, value);
  };
}

function attrFunction$1(name, value) {
  return function() {
    var v = value.apply(this, arguments);
    if (v == null) this.removeAttribute(name);
    else this.setAttribute(name, v);
  };
}

function attrFunctionNS$1(fullname, value) {
  return function() {
    var v = value.apply(this, arguments);
    if (v == null) this.removeAttributeNS(fullname.space, fullname.local);
    else this.setAttributeNS(fullname.space, fullname.local, v);
  };
}

function selection_attr(name, value) {
  var fullname = namespace(name);

  if (arguments.length < 2) {
    var node = this.node();
    return fullname.local
        ? node.getAttributeNS(fullname.space, fullname.local)
        : node.getAttribute(fullname);
  }

  return this.each((value == null
      ? (fullname.local ? attrRemoveNS$1 : attrRemove$1) : (typeof value === "function"
      ? (fullname.local ? attrFunctionNS$1 : attrFunction$1)
      : (fullname.local ? attrConstantNS$1 : attrConstant$1)))(fullname, value));
}

function defaultView(node) {
  return (node.ownerDocument && node.ownerDocument.defaultView) // node is a Node
      || (node.document && node) // node is a Window
      || node.defaultView; // node is a Document
}

function styleRemove$1(name) {
  return function() {
    this.style.removeProperty(name);
  };
}

function styleConstant$1(name, value, priority) {
  return function() {
    this.style.setProperty(name, value, priority);
  };
}

function styleFunction$1(name, value, priority) {
  return function() {
    var v = value.apply(this, arguments);
    if (v == null) this.style.removeProperty(name);
    else this.style.setProperty(name, v, priority);
  };
}

function selection_style(name, value, priority) {
  return arguments.length > 1
      ? this.each((value == null
            ? styleRemove$1 : typeof value === "function"
            ? styleFunction$1
            : styleConstant$1)(name, value, priority == null ? "" : priority))
      : styleValue(this.node(), name);
}

function styleValue(node, name) {
  return node.style.getPropertyValue(name)
      || defaultView(node).getComputedStyle(node, null).getPropertyValue(name);
}

function propertyRemove(name) {
  return function() {
    delete this[name];
  };
}

function propertyConstant(name, value) {
  return function() {
    this[name] = value;
  };
}

function propertyFunction(name, value) {
  return function() {
    var v = value.apply(this, arguments);
    if (v == null) delete this[name];
    else this[name] = v;
  };
}

function selection_property(name, value) {
  return arguments.length > 1
      ? this.each((value == null
          ? propertyRemove : typeof value === "function"
          ? propertyFunction
          : propertyConstant)(name, value))
      : this.node()[name];
}

function classArray(string) {
  return string.trim().split(/^|\s+/);
}

function classList(node) {
  return node.classList || new ClassList(node);
}

function ClassList(node) {
  this._node = node;
  this._names = classArray(node.getAttribute("class") || "");
}

ClassList.prototype = {
  add: function(name) {
    var i = this._names.indexOf(name);
    if (i < 0) {
      this._names.push(name);
      this._node.setAttribute("class", this._names.join(" "));
    }
  },
  remove: function(name) {
    var i = this._names.indexOf(name);
    if (i >= 0) {
      this._names.splice(i, 1);
      this._node.setAttribute("class", this._names.join(" "));
    }
  },
  contains: function(name) {
    return this._names.indexOf(name) >= 0;
  }
};

function classedAdd(node, names) {
  var list = classList(node), i = -1, n = names.length;
  while (++i < n) list.add(names[i]);
}

function classedRemove(node, names) {
  var list = classList(node), i = -1, n = names.length;
  while (++i < n) list.remove(names[i]);
}

function classedTrue(names) {
  return function() {
    classedAdd(this, names);
  };
}

function classedFalse(names) {
  return function() {
    classedRemove(this, names);
  };
}

function classedFunction(names, value) {
  return function() {
    (value.apply(this, arguments) ? classedAdd : classedRemove)(this, names);
  };
}

function selection_classed(name, value) {
  var names = classArray(name + "");

  if (arguments.length < 2) {
    var list = classList(this.node()), i = -1, n = names.length;
    while (++i < n) if (!list.contains(names[i])) return false;
    return true;
  }

  return this.each((typeof value === "function"
      ? classedFunction : value
      ? classedTrue
      : classedFalse)(names, value));
}

function textRemove() {
  this.textContent = "";
}

function textConstant$1(value) {
  return function() {
    this.textContent = value;
  };
}

function textFunction$1(value) {
  return function() {
    var v = value.apply(this, arguments);
    this.textContent = v == null ? "" : v;
  };
}

function selection_text(value) {
  return arguments.length
      ? this.each(value == null
          ? textRemove : (typeof value === "function"
          ? textFunction$1
          : textConstant$1)(value))
      : this.node().textContent;
}

function htmlRemove() {
  this.innerHTML = "";
}

function htmlConstant(value) {
  return function() {
    this.innerHTML = value;
  };
}

function htmlFunction(value) {
  return function() {
    var v = value.apply(this, arguments);
    this.innerHTML = v == null ? "" : v;
  };
}

function selection_html(value) {
  return arguments.length
      ? this.each(value == null
          ? htmlRemove : (typeof value === "function"
          ? htmlFunction
          : htmlConstant)(value))
      : this.node().innerHTML;
}

function raise() {
  if (this.nextSibling) this.parentNode.appendChild(this);
}

function selection_raise() {
  return this.each(raise);
}

function lower() {
  if (this.previousSibling) this.parentNode.insertBefore(this, this.parentNode.firstChild);
}

function selection_lower() {
  return this.each(lower);
}

function selection_append(name) {
  var create = typeof name === "function" ? name : creator(name);
  return this.select(function() {
    return this.appendChild(create.apply(this, arguments));
  });
}

function constantNull() {
  return null;
}

function selection_insert(name, before) {
  var create = typeof name === "function" ? name : creator(name),
      select = before == null ? constantNull : typeof before === "function" ? before : selector(before);
  return this.select(function() {
    return this.insertBefore(create.apply(this, arguments), select.apply(this, arguments) || null);
  });
}

function remove() {
  var parent = this.parentNode;
  if (parent) parent.removeChild(this);
}

function selection_remove() {
  return this.each(remove);
}

function selection_cloneShallow() {
  var clone = this.cloneNode(false), parent = this.parentNode;
  return parent ? parent.insertBefore(clone, this.nextSibling) : clone;
}

function selection_cloneDeep() {
  var clone = this.cloneNode(true), parent = this.parentNode;
  return parent ? parent.insertBefore(clone, this.nextSibling) : clone;
}

function selection_clone(deep) {
  return this.select(deep ? selection_cloneDeep : selection_cloneShallow);
}

function selection_datum(value) {
  return arguments.length
      ? this.property("__data__", value)
      : this.node().__data__;
}

function contextListener(listener) {
  return function(event) {
    listener.call(this, event, this.__data__);
  };
}

function parseTypenames$1(typenames) {
  return typenames.trim().split(/^|\s+/).map(function(t) {
    var name = "", i = t.indexOf(".");
    if (i >= 0) name = t.slice(i + 1), t = t.slice(0, i);
    return {type: t, name: name};
  });
}

function onRemove(typename) {
  return function() {
    var on = this.__on;
    if (!on) return;
    for (var j = 0, i = -1, m = on.length, o; j < m; ++j) {
      if (o = on[j], (!typename.type || o.type === typename.type) && o.name === typename.name) {
        this.removeEventListener(o.type, o.listener, o.options);
      } else {
        on[++i] = o;
      }
    }
    if (++i) on.length = i;
    else delete this.__on;
  };
}

function onAdd(typename, value, options) {
  return function() {
    var on = this.__on, o, listener = contextListener(value);
    if (on) for (var j = 0, m = on.length; j < m; ++j) {
      if ((o = on[j]).type === typename.type && o.name === typename.name) {
        this.removeEventListener(o.type, o.listener, o.options);
        this.addEventListener(o.type, o.listener = listener, o.options = options);
        o.value = value;
        return;
      }
    }
    this.addEventListener(typename.type, listener, options);
    o = {type: typename.type, name: typename.name, value: value, listener: listener, options: options};
    if (!on) this.__on = [o];
    else on.push(o);
  };
}

function selection_on(typename, value, options) {
  var typenames = parseTypenames$1(typename + ""), i, n = typenames.length, t;

  if (arguments.length < 2) {
    var on = this.node().__on;
    if (on) for (var j = 0, m = on.length, o; j < m; ++j) {
      for (i = 0, o = on[j]; i < n; ++i) {
        if ((t = typenames[i]).type === o.type && t.name === o.name) {
          return o.value;
        }
      }
    }
    return;
  }

  on = value ? onAdd : onRemove;
  for (i = 0; i < n; ++i) this.each(on(typenames[i], value, options));
  return this;
}

function dispatchEvent(node, type, params) {
  var window = defaultView(node),
      event = window.CustomEvent;

  if (typeof event === "function") {
    event = new event(type, params);
  } else {
    event = window.document.createEvent("Event");
    if (params) event.initEvent(type, params.bubbles, params.cancelable), event.detail = params.detail;
    else event.initEvent(type, false, false);
  }

  node.dispatchEvent(event);
}

function dispatchConstant(type, params) {
  return function() {
    return dispatchEvent(this, type, params);
  };
}

function dispatchFunction(type, params) {
  return function() {
    return dispatchEvent(this, type, params.apply(this, arguments));
  };
}

function selection_dispatch(type, params) {
  return this.each((typeof params === "function"
      ? dispatchFunction
      : dispatchConstant)(type, params));
}

function* selection_iterator() {
  for (var groups = this._groups, j = 0, m = groups.length; j < m; ++j) {
    for (var group = groups[j], i = 0, n = group.length, node; i < n; ++i) {
      if (node = group[i]) yield node;
    }
  }
}

var root = [null];

function Selection$1(groups, parents) {
  this._groups = groups;
  this._parents = parents;
}

function selection() {
  return new Selection$1([[document.documentElement]], root);
}

function selection_selection() {
  return this;
}

Selection$1.prototype = selection.prototype = {
  constructor: Selection$1,
  select: selection_select,
  selectAll: selection_selectAll,
  selectChild: selection_selectChild,
  selectChildren: selection_selectChildren,
  filter: selection_filter,
  data: selection_data,
  enter: selection_enter,
  exit: selection_exit,
  join: selection_join,
  merge: selection_merge,
  selection: selection_selection,
  order: selection_order,
  sort: selection_sort,
  call: selection_call,
  nodes: selection_nodes,
  node: selection_node,
  size: selection_size,
  empty: selection_empty,
  each: selection_each,
  attr: selection_attr,
  style: selection_style,
  property: selection_property,
  classed: selection_classed,
  text: selection_text,
  html: selection_html,
  raise: selection_raise,
  lower: selection_lower,
  append: selection_append,
  insert: selection_insert,
  remove: selection_remove,
  clone: selection_clone,
  datum: selection_datum,
  on: selection_on,
  dispatch: selection_dispatch,
  [Symbol.iterator]: selection_iterator
};

function select(selector) {
  return typeof selector === "string"
      ? new Selection$1([[document.querySelector(selector)]], [document.documentElement])
      : new Selection$1([[selector]], root);
}

function sourceEvent(event) {
  let sourceEvent;
  while (sourceEvent = event.sourceEvent) event = sourceEvent;
  return event;
}

function pointer(event, node) {
  event = sourceEvent(event);
  if (node === undefined) node = event.currentTarget;
  if (node) {
    var svg = node.ownerSVGElement || node;
    if (svg.createSVGPoint) {
      var point = svg.createSVGPoint();
      point.x = event.clientX, point.y = event.clientY;
      point = point.matrixTransform(node.getScreenCTM().inverse());
      return [point.x, point.y];
    }
    if (node.getBoundingClientRect) {
      var rect = node.getBoundingClientRect();
      return [event.clientX - rect.left - node.clientLeft, event.clientY - rect.top - node.clientTop];
    }
  }
  return [event.pageX, event.pageY];
}

var noop = {value: () => {}};

function dispatch() {
  for (var i = 0, n = arguments.length, _ = {}, t; i < n; ++i) {
    if (!(t = arguments[i] + "") || (t in _) || /[\s.]/.test(t)) throw new Error("illegal type: " + t);
    _[t] = [];
  }
  return new Dispatch(_);
}

function Dispatch(_) {
  this._ = _;
}

function parseTypenames(typenames, types) {
  return typenames.trim().split(/^|\s+/).map(function(t) {
    var name = "", i = t.indexOf(".");
    if (i >= 0) name = t.slice(i + 1), t = t.slice(0, i);
    if (t && !types.hasOwnProperty(t)) throw new Error("unknown type: " + t);
    return {type: t, name: name};
  });
}

Dispatch.prototype = dispatch.prototype = {
  constructor: Dispatch,
  on: function(typename, callback) {
    var _ = this._,
        T = parseTypenames(typename + "", _),
        t,
        i = -1,
        n = T.length;

    // If no callback was specified, return the callback of the given type and name.
    if (arguments.length < 2) {
      while (++i < n) if ((t = (typename = T[i]).type) && (t = get$1(_[t], typename.name))) return t;
      return;
    }

    // If a type was specified, set the callback for the given type and name.
    // Otherwise, if a null callback was specified, remove callbacks of the given name.
    if (callback != null && typeof callback !== "function") throw new Error("invalid callback: " + callback);
    while (++i < n) {
      if (t = (typename = T[i]).type) _[t] = set$1(_[t], typename.name, callback);
      else if (callback == null) for (t in _) _[t] = set$1(_[t], typename.name, null);
    }

    return this;
  },
  copy: function() {
    var copy = {}, _ = this._;
    for (var t in _) copy[t] = _[t].slice();
    return new Dispatch(copy);
  },
  call: function(type, that) {
    if ((n = arguments.length - 2) > 0) for (var args = new Array(n), i = 0, n, t; i < n; ++i) args[i] = arguments[i + 2];
    if (!this._.hasOwnProperty(type)) throw new Error("unknown type: " + type);
    for (t = this._[type], i = 0, n = t.length; i < n; ++i) t[i].value.apply(that, args);
  },
  apply: function(type, that, args) {
    if (!this._.hasOwnProperty(type)) throw new Error("unknown type: " + type);
    for (var t = this._[type], i = 0, n = t.length; i < n; ++i) t[i].value.apply(that, args);
  }
};

function get$1(type, name) {
  for (var i = 0, n = type.length, c; i < n; ++i) {
    if ((c = type[i]).name === name) {
      return c.value;
    }
  }
}

function set$1(type, name, callback) {
  for (var i = 0, n = type.length; i < n; ++i) {
    if (type[i].name === name) {
      type[i] = noop, type = type.slice(0, i).concat(type.slice(i + 1));
      break;
    }
  }
  if (callback != null) type.push({name: name, value: callback});
  return type;
}

// These are typically used in conjunction with noevent to ensure that we can
const nonpassivecapture = {capture: true, passive: false};

function noevent$1(event) {
  event.preventDefault();
  event.stopImmediatePropagation();
}

function dragDisable(view) {
  var root = view.document.documentElement,
      selection = select(view).on("dragstart.drag", noevent$1, nonpassivecapture);
  if ("onselectstart" in root) {
    selection.on("selectstart.drag", noevent$1, nonpassivecapture);
  } else {
    root.__noselect = root.style.MozUserSelect;
    root.style.MozUserSelect = "none";
  }
}

function yesdrag(view, noclick) {
  var root = view.document.documentElement,
      selection = select(view).on("dragstart.drag", null);
  if (noclick) {
    selection.on("click.drag", noevent$1, nonpassivecapture);
    setTimeout(function() { selection.on("click.drag", null); }, 0);
  }
  if ("onselectstart" in root) {
    selection.on("selectstart.drag", null);
  } else {
    root.style.MozUserSelect = root.__noselect;
    delete root.__noselect;
  }
}

function define(constructor, factory, prototype) {
  constructor.prototype = factory.prototype = prototype;
  prototype.constructor = constructor;
}

function extend(parent, definition) {
  var prototype = Object.create(parent.prototype);
  for (var key in definition) prototype[key] = definition[key];
  return prototype;
}

function Color() {}

var darker = 0.7;
var brighter = 1 / darker;

var reI = "\\s*([+-]?\\d+)\\s*",
    reN = "\\s*([+-]?(?:\\d*\\.)?\\d+(?:[eE][+-]?\\d+)?)\\s*",
    reP = "\\s*([+-]?(?:\\d*\\.)?\\d+(?:[eE][+-]?\\d+)?)%\\s*",
    reHex = /^#([0-9a-f]{3,8})$/,
    reRgbInteger = new RegExp(`^rgb\\(${reI},${reI},${reI}\\)$`),
    reRgbPercent = new RegExp(`^rgb\\(${reP},${reP},${reP}\\)$`),
    reRgbaInteger = new RegExp(`^rgba\\(${reI},${reI},${reI},${reN}\\)$`),
    reRgbaPercent = new RegExp(`^rgba\\(${reP},${reP},${reP},${reN}\\)$`),
    reHslPercent = new RegExp(`^hsl\\(${reN},${reP},${reP}\\)$`),
    reHslaPercent = new RegExp(`^hsla\\(${reN},${reP},${reP},${reN}\\)$`);

var named = {
  aliceblue: 0xf0f8ff,
  antiquewhite: 0xfaebd7,
  aqua: 0x00ffff,
  aquamarine: 0x7fffd4,
  azure: 0xf0ffff,
  beige: 0xf5f5dc,
  bisque: 0xffe4c4,
  black: 0x000000,
  blanchedalmond: 0xffebcd,
  blue: 0x0000ff,
  blueviolet: 0x8a2be2,
  brown: 0xa52a2a,
  burlywood: 0xdeb887,
  cadetblue: 0x5f9ea0,
  chartreuse: 0x7fff00,
  chocolate: 0xd2691e,
  coral: 0xff7f50,
  cornflowerblue: 0x6495ed,
  cornsilk: 0xfff8dc,
  crimson: 0xdc143c,
  cyan: 0x00ffff,
  darkblue: 0x00008b,
  darkcyan: 0x008b8b,
  darkgoldenrod: 0xb8860b,
  darkgray: 0xa9a9a9,
  darkgreen: 0x006400,
  darkgrey: 0xa9a9a9,
  darkkhaki: 0xbdb76b,
  darkmagenta: 0x8b008b,
  darkolivegreen: 0x556b2f,
  darkorange: 0xff8c00,
  darkorchid: 0x9932cc,
  darkred: 0x8b0000,
  darksalmon: 0xe9967a,
  darkseagreen: 0x8fbc8f,
  darkslateblue: 0x483d8b,
  darkslategray: 0x2f4f4f,
  darkslategrey: 0x2f4f4f,
  darkturquoise: 0x00ced1,
  darkviolet: 0x9400d3,
  deeppink: 0xff1493,
  deepskyblue: 0x00bfff,
  dimgray: 0x696969,
  dimgrey: 0x696969,
  dodgerblue: 0x1e90ff,
  firebrick: 0xb22222,
  floralwhite: 0xfffaf0,
  forestgreen: 0x228b22,
  fuchsia: 0xff00ff,
  gainsboro: 0xdcdcdc,
  ghostwhite: 0xf8f8ff,
  gold: 0xffd700,
  goldenrod: 0xdaa520,
  gray: 0x808080,
  green: 0x008000,
  greenyellow: 0xadff2f,
  grey: 0x808080,
  honeydew: 0xf0fff0,
  hotpink: 0xff69b4,
  indianred: 0xcd5c5c,
  indigo: 0x4b0082,
  ivory: 0xfffff0,
  khaki: 0xf0e68c,
  lavender: 0xe6e6fa,
  lavenderblush: 0xfff0f5,
  lawngreen: 0x7cfc00,
  lemonchiffon: 0xfffacd,
  lightblue: 0xadd8e6,
  lightcoral: 0xf08080,
  lightcyan: 0xe0ffff,
  lightgoldenrodyellow: 0xfafad2,
  lightgray: 0xd3d3d3,
  lightgreen: 0x90ee90,
  lightgrey: 0xd3d3d3,
  lightpink: 0xffb6c1,
  lightsalmon: 0xffa07a,
  lightseagreen: 0x20b2aa,
  lightskyblue: 0x87cefa,
  lightslategray: 0x778899,
  lightslategrey: 0x778899,
  lightsteelblue: 0xb0c4de,
  lightyellow: 0xffffe0,
  lime: 0x00ff00,
  limegreen: 0x32cd32,
  linen: 0xfaf0e6,
  magenta: 0xff00ff,
  maroon: 0x800000,
  mediumaquamarine: 0x66cdaa,
  mediumblue: 0x0000cd,
  mediumorchid: 0xba55d3,
  mediumpurple: 0x9370db,
  mediumseagreen: 0x3cb371,
  mediumslateblue: 0x7b68ee,
  mediumspringgreen: 0x00fa9a,
  mediumturquoise: 0x48d1cc,
  mediumvioletred: 0xc71585,
  midnightblue: 0x191970,
  mintcream: 0xf5fffa,
  mistyrose: 0xffe4e1,
  moccasin: 0xffe4b5,
  navajowhite: 0xffdead,
  navy: 0x000080,
  oldlace: 0xfdf5e6,
  olive: 0x808000,
  olivedrab: 0x6b8e23,
  orange: 0xffa500,
  orangered: 0xff4500,
  orchid: 0xda70d6,
  palegoldenrod: 0xeee8aa,
  palegreen: 0x98fb98,
  paleturquoise: 0xafeeee,
  palevioletred: 0xdb7093,
  papayawhip: 0xffefd5,
  peachpuff: 0xffdab9,
  peru: 0xcd853f,
  pink: 0xffc0cb,
  plum: 0xdda0dd,
  powderblue: 0xb0e0e6,
  purple: 0x800080,
  rebeccapurple: 0x663399,
  red: 0xff0000,
  rosybrown: 0xbc8f8f,
  royalblue: 0x4169e1,
  saddlebrown: 0x8b4513,
  salmon: 0xfa8072,
  sandybrown: 0xf4a460,
  seagreen: 0x2e8b57,
  seashell: 0xfff5ee,
  sienna: 0xa0522d,
  silver: 0xc0c0c0,
  skyblue: 0x87ceeb,
  slateblue: 0x6a5acd,
  slategray: 0x708090,
  slategrey: 0x708090,
  snow: 0xfffafa,
  springgreen: 0x00ff7f,
  steelblue: 0x4682b4,
  tan: 0xd2b48c,
  teal: 0x008080,
  thistle: 0xd8bfd8,
  tomato: 0xff6347,
  turquoise: 0x40e0d0,
  violet: 0xee82ee,
  wheat: 0xf5deb3,
  white: 0xffffff,
  whitesmoke: 0xf5f5f5,
  yellow: 0xffff00,
  yellowgreen: 0x9acd32
};

define(Color, color, {
  copy(channels) {
    return Object.assign(new this.constructor, this, channels);
  },
  displayable() {
    return this.rgb().displayable();
  },
  hex: color_formatHex, // Deprecated! Use color.formatHex.
  formatHex: color_formatHex,
  formatHex8: color_formatHex8,
  formatHsl: color_formatHsl,
  formatRgb: color_formatRgb,
  toString: color_formatRgb
});

function color_formatHex() {
  return this.rgb().formatHex();
}

function color_formatHex8() {
  return this.rgb().formatHex8();
}

function color_formatHsl() {
  return hslConvert(this).formatHsl();
}

function color_formatRgb() {
  return this.rgb().formatRgb();
}

function color(format) {
  var m, l;
  format = (format + "").trim().toLowerCase();
  return (m = reHex.exec(format)) ? (l = m[1].length, m = parseInt(m[1], 16), l === 6 ? rgbn(m) // #ff0000
      : l === 3 ? new Rgb((m >> 8 & 0xf) | (m >> 4 & 0xf0), (m >> 4 & 0xf) | (m & 0xf0), ((m & 0xf) << 4) | (m & 0xf), 1) // #f00
      : l === 8 ? rgba(m >> 24 & 0xff, m >> 16 & 0xff, m >> 8 & 0xff, (m & 0xff) / 0xff) // #ff000000
      : l === 4 ? rgba((m >> 12 & 0xf) | (m >> 8 & 0xf0), (m >> 8 & 0xf) | (m >> 4 & 0xf0), (m >> 4 & 0xf) | (m & 0xf0), (((m & 0xf) << 4) | (m & 0xf)) / 0xff) // #f000
      : null) // invalid hex
      : (m = reRgbInteger.exec(format)) ? new Rgb(m[1], m[2], m[3], 1) // rgb(255, 0, 0)
      : (m = reRgbPercent.exec(format)) ? new Rgb(m[1] * 255 / 100, m[2] * 255 / 100, m[3] * 255 / 100, 1) // rgb(100%, 0%, 0%)
      : (m = reRgbaInteger.exec(format)) ? rgba(m[1], m[2], m[3], m[4]) // rgba(255, 0, 0, 1)
      : (m = reRgbaPercent.exec(format)) ? rgba(m[1] * 255 / 100, m[2] * 255 / 100, m[3] * 255 / 100, m[4]) // rgb(100%, 0%, 0%, 1)
      : (m = reHslPercent.exec(format)) ? hsla(m[1], m[2] / 100, m[3] / 100, 1) // hsl(120, 50%, 50%)
      : (m = reHslaPercent.exec(format)) ? hsla(m[1], m[2] / 100, m[3] / 100, m[4]) // hsla(120, 50%, 50%, 1)
      : named.hasOwnProperty(format) ? rgbn(named[format]) // eslint-disable-line no-prototype-builtins
      : format === "transparent" ? new Rgb(NaN, NaN, NaN, 0)
      : null;
}

function rgbn(n) {
  return new Rgb(n >> 16 & 0xff, n >> 8 & 0xff, n & 0xff, 1);
}

function rgba(r, g, b, a) {
  if (a <= 0) r = g = b = NaN;
  return new Rgb(r, g, b, a);
}

function rgbConvert(o) {
  if (!(o instanceof Color)) o = color(o);
  if (!o) return new Rgb;
  o = o.rgb();
  return new Rgb(o.r, o.g, o.b, o.opacity);
}

function rgb(r, g, b, opacity) {
  return arguments.length === 1 ? rgbConvert(r) : new Rgb(r, g, b, opacity == null ? 1 : opacity);
}

function Rgb(r, g, b, opacity) {
  this.r = +r;
  this.g = +g;
  this.b = +b;
  this.opacity = +opacity;
}

define(Rgb, rgb, extend(Color, {
  brighter(k) {
    k = k == null ? brighter : Math.pow(brighter, k);
    return new Rgb(this.r * k, this.g * k, this.b * k, this.opacity);
  },
  darker(k) {
    k = k == null ? darker : Math.pow(darker, k);
    return new Rgb(this.r * k, this.g * k, this.b * k, this.opacity);
  },
  rgb() {
    return this;
  },
  clamp() {
    return new Rgb(clampi(this.r), clampi(this.g), clampi(this.b), clampa(this.opacity));
  },
  displayable() {
    return (-0.5 <= this.r && this.r < 255.5)
        && (-0.5 <= this.g && this.g < 255.5)
        && (-0.5 <= this.b && this.b < 255.5)
        && (0 <= this.opacity && this.opacity <= 1);
  },
  hex: rgb_formatHex, // Deprecated! Use color.formatHex.
  formatHex: rgb_formatHex,
  formatHex8: rgb_formatHex8,
  formatRgb: rgb_formatRgb,
  toString: rgb_formatRgb
}));

function rgb_formatHex() {
  return `#${hex(this.r)}${hex(this.g)}${hex(this.b)}`;
}

function rgb_formatHex8() {
  return `#${hex(this.r)}${hex(this.g)}${hex(this.b)}${hex((isNaN(this.opacity) ? 1 : this.opacity) * 255)}`;
}

function rgb_formatRgb() {
  const a = clampa(this.opacity);
  return `${a === 1 ? "rgb(" : "rgba("}${clampi(this.r)}, ${clampi(this.g)}, ${clampi(this.b)}${a === 1 ? ")" : `, ${a})`}`;
}

function clampa(opacity) {
  return isNaN(opacity) ? 1 : Math.max(0, Math.min(1, opacity));
}

function clampi(value) {
  return Math.max(0, Math.min(255, Math.round(value) || 0));
}

function hex(value) {
  value = clampi(value);
  return (value < 16 ? "0" : "") + value.toString(16);
}

function hsla(h, s, l, a) {
  if (a <= 0) h = s = l = NaN;
  else if (l <= 0 || l >= 1) h = s = NaN;
  else if (s <= 0) h = NaN;
  return new Hsl(h, s, l, a);
}

function hslConvert(o) {
  if (o instanceof Hsl) return new Hsl(o.h, o.s, o.l, o.opacity);
  if (!(o instanceof Color)) o = color(o);
  if (!o) return new Hsl;
  if (o instanceof Hsl) return o;
  o = o.rgb();
  var r = o.r / 255,
      g = o.g / 255,
      b = o.b / 255,
      min = Math.min(r, g, b),
      max = Math.max(r, g, b),
      h = NaN,
      s = max - min,
      l = (max + min) / 2;
  if (s) {
    if (r === max) h = (g - b) / s + (g < b) * 6;
    else if (g === max) h = (b - r) / s + 2;
    else h = (r - g) / s + 4;
    s /= l < 0.5 ? max + min : 2 - max - min;
    h *= 60;
  } else {
    s = l > 0 && l < 1 ? 0 : h;
  }
  return new Hsl(h, s, l, o.opacity);
}

function hsl(h, s, l, opacity) {
  return arguments.length === 1 ? hslConvert(h) : new Hsl(h, s, l, opacity == null ? 1 : opacity);
}

function Hsl(h, s, l, opacity) {
  this.h = +h;
  this.s = +s;
  this.l = +l;
  this.opacity = +opacity;
}

define(Hsl, hsl, extend(Color, {
  brighter(k) {
    k = k == null ? brighter : Math.pow(brighter, k);
    return new Hsl(this.h, this.s, this.l * k, this.opacity);
  },
  darker(k) {
    k = k == null ? darker : Math.pow(darker, k);
    return new Hsl(this.h, this.s, this.l * k, this.opacity);
  },
  rgb() {
    var h = this.h % 360 + (this.h < 0) * 360,
        s = isNaN(h) || isNaN(this.s) ? 0 : this.s,
        l = this.l,
        m2 = l + (l < 0.5 ? l : 1 - l) * s,
        m1 = 2 * l - m2;
    return new Rgb(
      hsl2rgb(h >= 240 ? h - 240 : h + 120, m1, m2),
      hsl2rgb(h, m1, m2),
      hsl2rgb(h < 120 ? h + 240 : h - 120, m1, m2),
      this.opacity
    );
  },
  clamp() {
    return new Hsl(clamph(this.h), clampt(this.s), clampt(this.l), clampa(this.opacity));
  },
  displayable() {
    return (0 <= this.s && this.s <= 1 || isNaN(this.s))
        && (0 <= this.l && this.l <= 1)
        && (0 <= this.opacity && this.opacity <= 1);
  },
  formatHsl() {
    const a = clampa(this.opacity);
    return `${a === 1 ? "hsl(" : "hsla("}${clamph(this.h)}, ${clampt(this.s) * 100}%, ${clampt(this.l) * 100}%${a === 1 ? ")" : `, ${a})`}`;
  }
}));

function clamph(value) {
  value = (value || 0) % 360;
  return value < 0 ? value + 360 : value;
}

function clampt(value) {
  return Math.max(0, Math.min(1, value || 0));
}

/* From FvD 13.37, CSS Color Module Level 3 */
function hsl2rgb(h, m1, m2) {
  return (h < 60 ? m1 + (m2 - m1) * h / 60
      : h < 180 ? m2
      : h < 240 ? m1 + (m2 - m1) * (240 - h) / 60
      : m1) * 255;
}

var constant$2 = x => () => x;

function linear(a, d) {
  return function(t) {
    return a + t * d;
  };
}

function exponential(a, b, y) {
  return a = Math.pow(a, y), b = Math.pow(b, y) - a, y = 1 / y, function(t) {
    return Math.pow(a + t * b, y);
  };
}

function gamma(y) {
  return (y = +y) === 1 ? nogamma : function(a, b) {
    return b - a ? exponential(a, b, y) : constant$2(isNaN(a) ? b : a);
  };
}

function nogamma(a, b) {
  var d = b - a;
  return d ? linear(a, d) : constant$2(isNaN(a) ? b : a);
}

var interpolateRgb = (function rgbGamma(y) {
  var color = gamma(y);

  function rgb$1(start, end) {
    var r = color((start = rgb(start)).r, (end = rgb(end)).r),
        g = color(start.g, end.g),
        b = color(start.b, end.b),
        opacity = nogamma(start.opacity, end.opacity);
    return function(t) {
      start.r = r(t);
      start.g = g(t);
      start.b = b(t);
      start.opacity = opacity(t);
      return start + "";
    };
  }

  rgb$1.gamma = rgbGamma;

  return rgb$1;
})(1);

function interpolateNumber(a, b) {
  return a = +a, b = +b, function(t) {
    return a * (1 - t) + b * t;
  };
}

var reA = /[-+]?(?:\d+\.?\d*|\.?\d+)(?:[eE][-+]?\d+)?/g,
    reB = new RegExp(reA.source, "g");

function zero(b) {
  return function() {
    return b;
  };
}

function one(b) {
  return function(t) {
    return b(t) + "";
  };
}

function interpolateString(a, b) {
  var bi = reA.lastIndex = reB.lastIndex = 0, // scan index for next number in b
      am, // current match in a
      bm, // current match in b
      bs, // string preceding current number in b, if any
      i = -1, // index in s
      s = [], // string constants and placeholders
      q = []; // number interpolators

  // Coerce inputs to strings.
  a = a + "", b = b + "";

  // Interpolate pairs of numbers in a & b.
  while ((am = reA.exec(a))
      && (bm = reB.exec(b))) {
    if ((bs = bm.index) > bi) { // a string precedes the next number in b
      bs = b.slice(bi, bs);
      if (s[i]) s[i] += bs; // coalesce with previous string
      else s[++i] = bs;
    }
    if ((am = am[0]) === (bm = bm[0])) { // numbers in a & b match
      if (s[i]) s[i] += bm; // coalesce with previous string
      else s[++i] = bm;
    } else { // interpolate non-matching numbers
      s[++i] = null;
      q.push({i: i, x: interpolateNumber(am, bm)});
    }
    bi = reB.lastIndex;
  }

  // Add remains of b.
  if (bi < b.length) {
    bs = b.slice(bi);
    if (s[i]) s[i] += bs; // coalesce with previous string
    else s[++i] = bs;
  }

  // Special optimization for only a single match.
  // Otherwise, interpolate each of the numbers and rejoin the string.
  return s.length < 2 ? (q[0]
      ? one(q[0].x)
      : zero(b))
      : (b = q.length, function(t) {
          for (var i = 0, o; i < b; ++i) s[(o = q[i]).i] = o.x(t);
          return s.join("");
        });
}

var degrees = 180 / Math.PI;

var identity$1 = {
  translateX: 0,
  translateY: 0,
  rotate: 0,
  skewX: 0,
  scaleX: 1,
  scaleY: 1
};

function decompose(a, b, c, d, e, f) {
  var scaleX, scaleY, skewX;
  if (scaleX = Math.sqrt(a * a + b * b)) a /= scaleX, b /= scaleX;
  if (skewX = a * c + b * d) c -= a * skewX, d -= b * skewX;
  if (scaleY = Math.sqrt(c * c + d * d)) c /= scaleY, d /= scaleY, skewX /= scaleY;
  if (a * d < b * c) a = -a, b = -b, skewX = -skewX, scaleX = -scaleX;
  return {
    translateX: e,
    translateY: f,
    rotate: Math.atan2(b, a) * degrees,
    skewX: Math.atan(skewX) * degrees,
    scaleX: scaleX,
    scaleY: scaleY
  };
}

var svgNode;

/* eslint-disable no-undef */
function parseCss(value) {
  const m = new (typeof DOMMatrix === "function" ? DOMMatrix : WebKitCSSMatrix)(value + "");
  return m.isIdentity ? identity$1 : decompose(m.a, m.b, m.c, m.d, m.e, m.f);
}

function parseSvg(value) {
  if (value == null) return identity$1;
  if (!svgNode) svgNode = document.createElementNS("http://www.w3.org/2000/svg", "g");
  svgNode.setAttribute("transform", value);
  if (!(value = svgNode.transform.baseVal.consolidate())) return identity$1;
  value = value.matrix;
  return decompose(value.a, value.b, value.c, value.d, value.e, value.f);
}

function interpolateTransform(parse, pxComma, pxParen, degParen) {

  function pop(s) {
    return s.length ? s.pop() + " " : "";
  }

  function translate(xa, ya, xb, yb, s, q) {
    if (xa !== xb || ya !== yb) {
      var i = s.push("translate(", null, pxComma, null, pxParen);
      q.push({i: i - 4, x: interpolateNumber(xa, xb)}, {i: i - 2, x: interpolateNumber(ya, yb)});
    } else if (xb || yb) {
      s.push("translate(" + xb + pxComma + yb + pxParen);
    }
  }

  function rotate(a, b, s, q) {
    if (a !== b) {
      if (a - b > 180) b += 360; else if (b - a > 180) a += 360; // shortest path
      q.push({i: s.push(pop(s) + "rotate(", null, degParen) - 2, x: interpolateNumber(a, b)});
    } else if (b) {
      s.push(pop(s) + "rotate(" + b + degParen);
    }
  }

  function skewX(a, b, s, q) {
    if (a !== b) {
      q.push({i: s.push(pop(s) + "skewX(", null, degParen) - 2, x: interpolateNumber(a, b)});
    } else if (b) {
      s.push(pop(s) + "skewX(" + b + degParen);
    }
  }

  function scale(xa, ya, xb, yb, s, q) {
    if (xa !== xb || ya !== yb) {
      var i = s.push(pop(s) + "scale(", null, ",", null, ")");
      q.push({i: i - 4, x: interpolateNumber(xa, xb)}, {i: i - 2, x: interpolateNumber(ya, yb)});
    } else if (xb !== 1 || yb !== 1) {
      s.push(pop(s) + "scale(" + xb + "," + yb + ")");
    }
  }

  return function(a, b) {
    var s = [], // string constants and placeholders
        q = []; // number interpolators
    a = parse(a), b = parse(b);
    translate(a.translateX, a.translateY, b.translateX, b.translateY, s, q);
    rotate(a.rotate, b.rotate, s, q);
    skewX(a.skewX, b.skewX, s, q);
    scale(a.scaleX, a.scaleY, b.scaleX, b.scaleY, s, q);
    a = b = null; // gc
    return function(t) {
      var i = -1, n = q.length, o;
      while (++i < n) s[(o = q[i]).i] = o.x(t);
      return s.join("");
    };
  };
}

var interpolateTransformCss = interpolateTransform(parseCss, "px, ", "px)", "deg)");
var interpolateTransformSvg = interpolateTransform(parseSvg, ", ", ")", ")");

var epsilon2 = 1e-12;

function cosh(x) {
  return ((x = Math.exp(x)) + 1 / x) / 2;
}

function sinh(x) {
  return ((x = Math.exp(x)) - 1 / x) / 2;
}

function tanh(x) {
  return ((x = Math.exp(2 * x)) - 1) / (x + 1);
}

var interpolateZoom = (function zoomRho(rho, rho2, rho4) {

  // p0 = [ux0, uy0, w0]
  // p1 = [ux1, uy1, w1]
  function zoom(p0, p1) {
    var ux0 = p0[0], uy0 = p0[1], w0 = p0[2],
        ux1 = p1[0], uy1 = p1[1], w1 = p1[2],
        dx = ux1 - ux0,
        dy = uy1 - uy0,
        d2 = dx * dx + dy * dy,
        i,
        S;

    // Special case for u0 ≅ u1.
    if (d2 < epsilon2) {
      S = Math.log(w1 / w0) / rho;
      i = function(t) {
        return [
          ux0 + t * dx,
          uy0 + t * dy,
          w0 * Math.exp(rho * t * S)
        ];
      };
    }

    // General case.
    else {
      var d1 = Math.sqrt(d2),
          b0 = (w1 * w1 - w0 * w0 + rho4 * d2) / (2 * w0 * rho2 * d1),
          b1 = (w1 * w1 - w0 * w0 - rho4 * d2) / (2 * w1 * rho2 * d1),
          r0 = Math.log(Math.sqrt(b0 * b0 + 1) - b0),
          r1 = Math.log(Math.sqrt(b1 * b1 + 1) - b1);
      S = (r1 - r0) / rho;
      i = function(t) {
        var s = t * S,
            coshr0 = cosh(r0),
            u = w0 / (rho2 * d1) * (coshr0 * tanh(rho * s + r0) - sinh(r0));
        return [
          ux0 + u * dx,
          uy0 + u * dy,
          w0 * coshr0 / cosh(rho * s + r0)
        ];
      };
    }

    i.duration = S * 1000 * rho / Math.SQRT2;

    return i;
  }

  zoom.rho = function(_) {
    var _1 = Math.max(1e-3, +_), _2 = _1 * _1, _4 = _2 * _2;
    return zoomRho(_1, _2, _4);
  };

  return zoom;
})(Math.SQRT2, 2, 4);

var frame = 0, // is an animation frame pending?
    timeout$1 = 0, // is a timeout pending?
    interval = 0, // are any timers active?
    pokeDelay = 1000, // how frequently we check for clock skew
    taskHead,
    taskTail,
    clockLast = 0,
    clockNow = 0,
    clockSkew = 0,
    clock = typeof performance === "object" && performance.now ? performance : Date,
    setFrame = window.requestAnimationFrame ? window.requestAnimationFrame.bind(window) : function(f) { setTimeout(f, 17); };

function now() {
  return clockNow || (setFrame(clearNow), clockNow = clock.now() + clockSkew);
}

function clearNow() {
  clockNow = 0;
}

function Timer() {
  this._call =
  this._time =
  this._next = null;
}

Timer.prototype = timer.prototype = {
  constructor: Timer,
  restart: function(callback, delay, time) {
    if (typeof callback !== "function") throw new TypeError("callback is not a function");
    time = (time == null ? now() : +time) + (delay == null ? 0 : +delay);
    if (!this._next && taskTail !== this) {
      if (taskTail) taskTail._next = this;
      else taskHead = this;
      taskTail = this;
    }
    this._call = callback;
    this._time = time;
    sleep();
  },
  stop: function() {
    if (this._call) {
      this._call = null;
      this._time = Infinity;
      sleep();
    }
  }
};

function timer(callback, delay, time) {
  var t = new Timer;
  t.restart(callback, delay, time);
  return t;
}

function timerFlush() {
  now(); // Get the current time, if not already set.
  ++frame; // Pretend we’ve set an alarm, if we haven’t already.
  var t = taskHead, e;
  while (t) {
    if ((e = clockNow - t._time) >= 0) t._call.call(undefined, e);
    t = t._next;
  }
  --frame;
}

function wake() {
  clockNow = (clockLast = clock.now()) + clockSkew;
  frame = timeout$1 = 0;
  try {
    timerFlush();
  } finally {
    frame = 0;
    nap();
    clockNow = 0;
  }
}

function poke() {
  var now = clock.now(), delay = now - clockLast;
  if (delay > pokeDelay) clockSkew -= delay, clockLast = now;
}

function nap() {
  var t0, t1 = taskHead, t2, time = Infinity;
  while (t1) {
    if (t1._call) {
      if (time > t1._time) time = t1._time;
      t0 = t1, t1 = t1._next;
    } else {
      t2 = t1._next, t1._next = null;
      t1 = t0 ? t0._next = t2 : taskHead = t2;
    }
  }
  taskTail = t0;
  sleep(time);
}

function sleep(time) {
  if (frame) return; // Soonest alarm already set, or will be.
  if (timeout$1) timeout$1 = clearTimeout(timeout$1);
  var delay = time - clockNow; // Strictly less than if we recomputed clockNow.
  if (delay > 24) {
    if (time < Infinity) timeout$1 = setTimeout(wake, time - clock.now() - clockSkew);
    if (interval) interval = clearInterval(interval);
  } else {
    if (!interval) clockLast = clock.now(), interval = setInterval(poke, pokeDelay);
    frame = 1, setFrame(wake);
  }
}

function timeout(callback, delay, time) {
  var t = new Timer;
  delay = delay == null ? 0 : +delay;
  t.restart(elapsed => {
    t.stop();
    callback(elapsed + delay);
  }, delay, time);
  return t;
}

var emptyOn = dispatch("start", "end", "cancel", "interrupt");
var emptyTween = [];

var CREATED = 0;
var SCHEDULED = 1;
var STARTING = 2;
var STARTED = 3;
var RUNNING = 4;
var ENDING = 5;
var ENDED = 6;

function schedule(node, name, id, index, group, timing) {
  var schedules = node.__transition;
  if (!schedules) node.__transition = {};
  else if (id in schedules) return;
  create(node, id, {
    name: name,
    index: index, // For context during callback.
    group: group, // For context during callback.
    on: emptyOn,
    tween: emptyTween,
    time: timing.time,
    delay: timing.delay,
    duration: timing.duration,
    ease: timing.ease,
    timer: null,
    state: CREATED
  });
}

function init(node, id) {
  var schedule = get(node, id);
  if (schedule.state > CREATED) throw new Error("too late; already scheduled");
  return schedule;
}

function set(node, id) {
  var schedule = get(node, id);
  if (schedule.state > STARTED) throw new Error("too late; already running");
  return schedule;
}

function get(node, id) {
  var schedule = node.__transition;
  if (!schedule || !(schedule = schedule[id])) throw new Error("transition not found");
  return schedule;
}

function create(node, id, self) {
  var schedules = node.__transition,
      tween;

  // Initialize the self timer when the transition is created.
  // Note the actual delay is not known until the first callback!
  schedules[id] = self;
  self.timer = timer(schedule, 0, self.time);

  function schedule(elapsed) {
    self.state = SCHEDULED;
    self.timer.restart(start, self.delay, self.time);

    // If the elapsed delay is less than our first sleep, start immediately.
    if (self.delay <= elapsed) start(elapsed - self.delay);
  }

  function start(elapsed) {
    var i, j, n, o;

    // If the state is not SCHEDULED, then we previously errored on start.
    if (self.state !== SCHEDULED) return stop();

    for (i in schedules) {
      o = schedules[i];
      if (o.name !== self.name) continue;

      // While this element already has a starting transition during this frame,
      // defer starting an interrupting transition until that transition has a
      // chance to tick (and possibly end); see d3/d3-transition#54!
      if (o.state === STARTED) return timeout(start);

      // Interrupt the active transition, if any.
      if (o.state === RUNNING) {
        o.state = ENDED;
        o.timer.stop();
        o.on.call("interrupt", node, node.__data__, o.index, o.group);
        delete schedules[i];
      }

      // Cancel any pre-empted transitions.
      else if (+i < id) {
        o.state = ENDED;
        o.timer.stop();
        o.on.call("cancel", node, node.__data__, o.index, o.group);
        delete schedules[i];
      }
    }

    // Defer the first tick to end of the current frame; see d3/d3#1576.
    // Note the transition may be canceled after start and before the first tick!
    // Note this must be scheduled before the start event; see d3/d3-transition#16!
    // Assuming this is successful, subsequent callbacks go straight to tick.
    timeout(function() {
      if (self.state === STARTED) {
        self.state = RUNNING;
        self.timer.restart(tick, self.delay, self.time);
        tick(elapsed);
      }
    });

    // Dispatch the start event.
    // Note this must be done before the tween are initialized.
    self.state = STARTING;
    self.on.call("start", node, node.__data__, self.index, self.group);
    if (self.state !== STARTING) return; // interrupted
    self.state = STARTED;

    // Initialize the tween, deleting null tween.
    tween = new Array(n = self.tween.length);
    for (i = 0, j = -1; i < n; ++i) {
      if (o = self.tween[i].value.call(node, node.__data__, self.index, self.group)) {
        tween[++j] = o;
      }
    }
    tween.length = j + 1;
  }

  function tick(elapsed) {
    var t = elapsed < self.duration ? self.ease.call(null, elapsed / self.duration) : (self.timer.restart(stop), self.state = ENDING, 1),
        i = -1,
        n = tween.length;

    while (++i < n) {
      tween[i].call(node, t);
    }

    // Dispatch the end event.
    if (self.state === ENDING) {
      self.on.call("end", node, node.__data__, self.index, self.group);
      stop();
    }
  }

  function stop() {
    self.state = ENDED;
    self.timer.stop();
    delete schedules[id];
    for (var i in schedules) return; // eslint-disable-line no-unused-vars
    delete node.__transition;
  }
}

function interrupt(node, name) {
  var schedules = node.__transition,
      schedule,
      active,
      empty = true,
      i;

  if (!schedules) return;

  name = name == null ? null : name + "";

  for (i in schedules) {
    if ((schedule = schedules[i]).name !== name) { empty = false; continue; }
    active = schedule.state > STARTING && schedule.state < ENDING;
    schedule.state = ENDED;
    schedule.timer.stop();
    schedule.on.call(active ? "interrupt" : "cancel", node, node.__data__, schedule.index, schedule.group);
    delete schedules[i];
  }

  if (empty) delete node.__transition;
}

function selection_interrupt(name) {
  return this.each(function() {
    interrupt(this, name);
  });
}

function tweenRemove(id, name) {
  var tween0, tween1;
  return function() {
    var schedule = set(this, id),
        tween = schedule.tween;

    // If this node shared tween with the previous node,
    // just assign the updated shared tween and we’re done!
    // Otherwise, copy-on-write.
    if (tween !== tween0) {
      tween1 = tween0 = tween;
      for (var i = 0, n = tween1.length; i < n; ++i) {
        if (tween1[i].name === name) {
          tween1 = tween1.slice();
          tween1.splice(i, 1);
          break;
        }
      }
    }

    schedule.tween = tween1;
  };
}

function tweenFunction(id, name, value) {
  var tween0, tween1;
  if (typeof value !== "function") throw new Error;
  return function() {
    var schedule = set(this, id),
        tween = schedule.tween;

    // If this node shared tween with the previous node,
    // just assign the updated shared tween and we’re done!
    // Otherwise, copy-on-write.
    if (tween !== tween0) {
      tween1 = (tween0 = tween).slice();
      for (var t = {name: name, value: value}, i = 0, n = tween1.length; i < n; ++i) {
        if (tween1[i].name === name) {
          tween1[i] = t;
          break;
        }
      }
      if (i === n) tween1.push(t);
    }

    schedule.tween = tween1;
  };
}

function transition_tween(name, value) {
  var id = this._id;

  name += "";

  if (arguments.length < 2) {
    var tween = get(this.node(), id).tween;
    for (var i = 0, n = tween.length, t; i < n; ++i) {
      if ((t = tween[i]).name === name) {
        return t.value;
      }
    }
    return null;
  }

  return this.each((value == null ? tweenRemove : tweenFunction)(id, name, value));
}

function tweenValue(transition, name, value) {
  var id = transition._id;

  transition.each(function() {
    var schedule = set(this, id);
    (schedule.value || (schedule.value = {}))[name] = value.apply(this, arguments);
  });

  return function(node) {
    return get(node, id).value[name];
  };
}

function interpolate(a, b) {
  var c;
  return (typeof b === "number" ? interpolateNumber
      : b instanceof color ? interpolateRgb
      : (c = color(b)) ? (b = c, interpolateRgb)
      : interpolateString)(a, b);
}

function attrRemove(name) {
  return function() {
    this.removeAttribute(name);
  };
}

function attrRemoveNS(fullname) {
  return function() {
    this.removeAttributeNS(fullname.space, fullname.local);
  };
}

function attrConstant(name, interpolate, value1) {
  var string00,
      string1 = value1 + "",
      interpolate0;
  return function() {
    var string0 = this.getAttribute(name);
    return string0 === string1 ? null
        : string0 === string00 ? interpolate0
        : interpolate0 = interpolate(string00 = string0, value1);
  };
}

function attrConstantNS(fullname, interpolate, value1) {
  var string00,
      string1 = value1 + "",
      interpolate0;
  return function() {
    var string0 = this.getAttributeNS(fullname.space, fullname.local);
    return string0 === string1 ? null
        : string0 === string00 ? interpolate0
        : interpolate0 = interpolate(string00 = string0, value1);
  };
}

function attrFunction(name, interpolate, value) {
  var string00,
      string10,
      interpolate0;
  return function() {
    var string0, value1 = value(this), string1;
    if (value1 == null) return void this.removeAttribute(name);
    string0 = this.getAttribute(name);
    string1 = value1 + "";
    return string0 === string1 ? null
        : string0 === string00 && string1 === string10 ? interpolate0
        : (string10 = string1, interpolate0 = interpolate(string00 = string0, value1));
  };
}

function attrFunctionNS(fullname, interpolate, value) {
  var string00,
      string10,
      interpolate0;
  return function() {
    var string0, value1 = value(this), string1;
    if (value1 == null) return void this.removeAttributeNS(fullname.space, fullname.local);
    string0 = this.getAttributeNS(fullname.space, fullname.local);
    string1 = value1 + "";
    return string0 === string1 ? null
        : string0 === string00 && string1 === string10 ? interpolate0
        : (string10 = string1, interpolate0 = interpolate(string00 = string0, value1));
  };
}

function transition_attr(name, value) {
  var fullname = namespace(name), i = fullname === "transform" ? interpolateTransformSvg : interpolate;
  return this.attrTween(name, typeof value === "function"
      ? (fullname.local ? attrFunctionNS : attrFunction)(fullname, i, tweenValue(this, "attr." + name, value))
      : value == null ? (fullname.local ? attrRemoveNS : attrRemove)(fullname)
      : (fullname.local ? attrConstantNS : attrConstant)(fullname, i, value));
}

function attrInterpolate(name, i) {
  return function(t) {
    this.setAttribute(name, i.call(this, t));
  };
}

function attrInterpolateNS(fullname, i) {
  return function(t) {
    this.setAttributeNS(fullname.space, fullname.local, i.call(this, t));
  };
}

function attrTweenNS(fullname, value) {
  var t0, i0;
  function tween() {
    var i = value.apply(this, arguments);
    if (i !== i0) t0 = (i0 = i) && attrInterpolateNS(fullname, i);
    return t0;
  }
  tween._value = value;
  return tween;
}

function attrTween(name, value) {
  var t0, i0;
  function tween() {
    var i = value.apply(this, arguments);
    if (i !== i0) t0 = (i0 = i) && attrInterpolate(name, i);
    return t0;
  }
  tween._value = value;
  return tween;
}

function transition_attrTween(name, value) {
  var key = "attr." + name;
  if (arguments.length < 2) return (key = this.tween(key)) && key._value;
  if (value == null) return this.tween(key, null);
  if (typeof value !== "function") throw new Error;
  var fullname = namespace(name);
  return this.tween(key, (fullname.local ? attrTweenNS : attrTween)(fullname, value));
}

function delayFunction(id, value) {
  return function() {
    init(this, id).delay = +value.apply(this, arguments);
  };
}

function delayConstant(id, value) {
  return value = +value, function() {
    init(this, id).delay = value;
  };
}

function transition_delay(value) {
  var id = this._id;

  return arguments.length
      ? this.each((typeof value === "function"
          ? delayFunction
          : delayConstant)(id, value))
      : get(this.node(), id).delay;
}

function durationFunction(id, value) {
  return function() {
    set(this, id).duration = +value.apply(this, arguments);
  };
}

function durationConstant(id, value) {
  return value = +value, function() {
    set(this, id).duration = value;
  };
}

function transition_duration(value) {
  var id = this._id;

  return arguments.length
      ? this.each((typeof value === "function"
          ? durationFunction
          : durationConstant)(id, value))
      : get(this.node(), id).duration;
}

function easeConstant(id, value) {
  if (typeof value !== "function") throw new Error;
  return function() {
    set(this, id).ease = value;
  };
}

function transition_ease(value) {
  var id = this._id;

  return arguments.length
      ? this.each(easeConstant(id, value))
      : get(this.node(), id).ease;
}

function easeVarying(id, value) {
  return function() {
    var v = value.apply(this, arguments);
    if (typeof v !== "function") throw new Error;
    set(this, id).ease = v;
  };
}

function transition_easeVarying(value) {
  if (typeof value !== "function") throw new Error;
  return this.each(easeVarying(this._id, value));
}

function transition_filter(match) {
  if (typeof match !== "function") match = matcher(match);

  for (var groups = this._groups, m = groups.length, subgroups = new Array(m), j = 0; j < m; ++j) {
    for (var group = groups[j], n = group.length, subgroup = subgroups[j] = [], node, i = 0; i < n; ++i) {
      if ((node = group[i]) && match.call(node, node.__data__, i, group)) {
        subgroup.push(node);
      }
    }
  }

  return new Transition(subgroups, this._parents, this._name, this._id);
}

function transition_merge(transition) {
  if (transition._id !== this._id) throw new Error;

  for (var groups0 = this._groups, groups1 = transition._groups, m0 = groups0.length, m1 = groups1.length, m = Math.min(m0, m1), merges = new Array(m0), j = 0; j < m; ++j) {
    for (var group0 = groups0[j], group1 = groups1[j], n = group0.length, merge = merges[j] = new Array(n), node, i = 0; i < n; ++i) {
      if (node = group0[i] || group1[i]) {
        merge[i] = node;
      }
    }
  }

  for (; j < m0; ++j) {
    merges[j] = groups0[j];
  }

  return new Transition(merges, this._parents, this._name, this._id);
}

function start(name) {
  return (name + "").trim().split(/^|\s+/).every(function(t) {
    var i = t.indexOf(".");
    if (i >= 0) t = t.slice(0, i);
    return !t || t === "start";
  });
}

function onFunction(id, name, listener) {
  var on0, on1, sit = start(name) ? init : set;
  return function() {
    var schedule = sit(this, id),
        on = schedule.on;

    // If this node shared a dispatch with the previous node,
    // just assign the updated shared dispatch and we’re done!
    // Otherwise, copy-on-write.
    if (on !== on0) (on1 = (on0 = on).copy()).on(name, listener);

    schedule.on = on1;
  };
}

function transition_on(name, listener) {
  var id = this._id;

  return arguments.length < 2
      ? get(this.node(), id).on.on(name)
      : this.each(onFunction(id, name, listener));
}

function removeFunction(id) {
  return function() {
    var parent = this.parentNode;
    for (var i in this.__transition) if (+i !== id) return;
    if (parent) parent.removeChild(this);
  };
}

function transition_remove() {
  return this.on("end.remove", removeFunction(this._id));
}

function transition_select(select) {
  var name = this._name,
      id = this._id;

  if (typeof select !== "function") select = selector(select);

  for (var groups = this._groups, m = groups.length, subgroups = new Array(m), j = 0; j < m; ++j) {
    for (var group = groups[j], n = group.length, subgroup = subgroups[j] = new Array(n), node, subnode, i = 0; i < n; ++i) {
      if ((node = group[i]) && (subnode = select.call(node, node.__data__, i, group))) {
        if ("__data__" in node) subnode.__data__ = node.__data__;
        subgroup[i] = subnode;
        schedule(subgroup[i], name, id, i, subgroup, get(node, id));
      }
    }
  }

  return new Transition(subgroups, this._parents, name, id);
}

function transition_selectAll(select) {
  var name = this._name,
      id = this._id;

  if (typeof select !== "function") select = selectorAll(select);

  for (var groups = this._groups, m = groups.length, subgroups = [], parents = [], j = 0; j < m; ++j) {
    for (var group = groups[j], n = group.length, node, i = 0; i < n; ++i) {
      if (node = group[i]) {
        for (var children = select.call(node, node.__data__, i, group), child, inherit = get(node, id), k = 0, l = children.length; k < l; ++k) {
          if (child = children[k]) {
            schedule(child, name, id, k, children, inherit);
          }
        }
        subgroups.push(children);
        parents.push(node);
      }
    }
  }

  return new Transition(subgroups, parents, name, id);
}

var Selection = selection.prototype.constructor;

function transition_selection() {
  return new Selection(this._groups, this._parents);
}

function styleNull(name, interpolate) {
  var string00,
      string10,
      interpolate0;
  return function() {
    var string0 = styleValue(this, name),
        string1 = (this.style.removeProperty(name), styleValue(this, name));
    return string0 === string1 ? null
        : string0 === string00 && string1 === string10 ? interpolate0
        : interpolate0 = interpolate(string00 = string0, string10 = string1);
  };
}

function styleRemove(name) {
  return function() {
    this.style.removeProperty(name);
  };
}

function styleConstant(name, interpolate, value1) {
  var string00,
      string1 = value1 + "",
      interpolate0;
  return function() {
    var string0 = styleValue(this, name);
    return string0 === string1 ? null
        : string0 === string00 ? interpolate0
        : interpolate0 = interpolate(string00 = string0, value1);
  };
}

function styleFunction(name, interpolate, value) {
  var string00,
      string10,
      interpolate0;
  return function() {
    var string0 = styleValue(this, name),
        value1 = value(this),
        string1 = value1 + "";
    if (value1 == null) string1 = value1 = (this.style.removeProperty(name), styleValue(this, name));
    return string0 === string1 ? null
        : string0 === string00 && string1 === string10 ? interpolate0
        : (string10 = string1, interpolate0 = interpolate(string00 = string0, value1));
  };
}

function styleMaybeRemove(id, name) {
  var on0, on1, listener0, key = "style." + name, event = "end." + key, remove;
  return function() {
    var schedule = set(this, id),
        on = schedule.on,
        listener = schedule.value[key] == null ? remove || (remove = styleRemove(name)) : undefined;

    // If this node shared a dispatch with the previous node,
    // just assign the updated shared dispatch and we’re done!
    // Otherwise, copy-on-write.
    if (on !== on0 || listener0 !== listener) (on1 = (on0 = on).copy()).on(event, listener0 = listener);

    schedule.on = on1;
  };
}

function transition_style(name, value, priority) {
  var i = (name += "") === "transform" ? interpolateTransformCss : interpolate;
  return value == null ? this
      .styleTween(name, styleNull(name, i))
      .on("end.style." + name, styleRemove(name))
    : typeof value === "function" ? this
      .styleTween(name, styleFunction(name, i, tweenValue(this, "style." + name, value)))
      .each(styleMaybeRemove(this._id, name))
    : this
      .styleTween(name, styleConstant(name, i, value), priority)
      .on("end.style." + name, null);
}

function styleInterpolate(name, i, priority) {
  return function(t) {
    this.style.setProperty(name, i.call(this, t), priority);
  };
}

function styleTween(name, value, priority) {
  var t, i0;
  function tween() {
    var i = value.apply(this, arguments);
    if (i !== i0) t = (i0 = i) && styleInterpolate(name, i, priority);
    return t;
  }
  tween._value = value;
  return tween;
}

function transition_styleTween(name, value, priority) {
  var key = "style." + (name += "");
  if (arguments.length < 2) return (key = this.tween(key)) && key._value;
  if (value == null) return this.tween(key, null);
  if (typeof value !== "function") throw new Error;
  return this.tween(key, styleTween(name, value, priority == null ? "" : priority));
}

function textConstant(value) {
  return function() {
    this.textContent = value;
  };
}

function textFunction(value) {
  return function() {
    var value1 = value(this);
    this.textContent = value1 == null ? "" : value1;
  };
}

function transition_text(value) {
  return this.tween("text", typeof value === "function"
      ? textFunction(tweenValue(this, "text", value))
      : textConstant(value == null ? "" : value + ""));
}

function textInterpolate(i) {
  return function(t) {
    this.textContent = i.call(this, t);
  };
}

function textTween(value) {
  var t0, i0;
  function tween() {
    var i = value.apply(this, arguments);
    if (i !== i0) t0 = (i0 = i) && textInterpolate(i);
    return t0;
  }
  tween._value = value;
  return tween;
}

function transition_textTween(value) {
  var key = "text";
  if (arguments.length < 1) return (key = this.tween(key)) && key._value;
  if (value == null) return this.tween(key, null);
  if (typeof value !== "function") throw new Error;
  return this.tween(key, textTween(value));
}

function transition_transition() {
  var name = this._name,
      id0 = this._id,
      id1 = newId();

  for (var groups = this._groups, m = groups.length, j = 0; j < m; ++j) {
    for (var group = groups[j], n = group.length, node, i = 0; i < n; ++i) {
      if (node = group[i]) {
        var inherit = get(node, id0);
        schedule(node, name, id1, i, group, {
          time: inherit.time + inherit.delay + inherit.duration,
          delay: 0,
          duration: inherit.duration,
          ease: inherit.ease
        });
      }
    }
  }

  return new Transition(groups, this._parents, name, id1);
}

function transition_end() {
  var on0, on1, that = this, id = that._id, size = that.size();
  return new Promise(function(resolve, reject) {
    var cancel = {value: reject},
        end = {value: function() { if (--size === 0) resolve(); }};

    that.each(function() {
      var schedule = set(this, id),
          on = schedule.on;

      // If this node shared a dispatch with the previous node,
      // just assign the updated shared dispatch and we’re done!
      // Otherwise, copy-on-write.
      if (on !== on0) {
        on1 = (on0 = on).copy();
        on1._.cancel.push(cancel);
        on1._.interrupt.push(cancel);
        on1._.end.push(end);
      }

      schedule.on = on1;
    });

    // The selection was empty, resolve end immediately
    if (size === 0) resolve();
  });
}

var id = 0;

function Transition(groups, parents, name, id) {
  this._groups = groups;
  this._parents = parents;
  this._name = name;
  this._id = id;
}

function newId() {
  return ++id;
}

var selection_prototype = selection.prototype;

Transition.prototype = {
  constructor: Transition,
  select: transition_select,
  selectAll: transition_selectAll,
  selectChild: selection_prototype.selectChild,
  selectChildren: selection_prototype.selectChildren,
  filter: transition_filter,
  merge: transition_merge,
  selection: transition_selection,
  transition: transition_transition,
  call: selection_prototype.call,
  nodes: selection_prototype.nodes,
  node: selection_prototype.node,
  size: selection_prototype.size,
  empty: selection_prototype.empty,
  each: selection_prototype.each,
  on: transition_on,
  attr: transition_attr,
  attrTween: transition_attrTween,
  style: transition_style,
  styleTween: transition_styleTween,
  text: transition_text,
  textTween: transition_textTween,
  remove: transition_remove,
  tween: transition_tween,
  delay: transition_delay,
  duration: transition_duration,
  ease: transition_ease,
  easeVarying: transition_easeVarying,
  end: transition_end,
  [Symbol.iterator]: selection_prototype[Symbol.iterator]
};

function cubicInOut(t) {
  return ((t *= 2) <= 1 ? t * t * t : (t -= 2) * t * t + 2) / 2;
}

var defaultTiming = {
  time: null, // Set on use.
  delay: 0,
  duration: 250,
  ease: cubicInOut
};

function inherit(node, id) {
  var timing;
  while (!(timing = node.__transition) || !(timing = timing[id])) {
    if (!(node = node.parentNode)) {
      throw new Error(`transition ${id} not found`);
    }
  }
  return timing;
}

function selection_transition(name) {
  var id,
      timing;

  if (name instanceof Transition) {
    id = name._id, name = name._name;
  } else {
    id = newId(), (timing = defaultTiming).time = now(), name = name == null ? null : name + "";
  }

  for (var groups = this._groups, m = groups.length, j = 0; j < m; ++j) {
    for (var group = groups[j], n = group.length, node, i = 0; i < n; ++i) {
      if (node = group[i]) {
        schedule(node, name, id, i, group, timing || inherit(node, id));
      }
    }
  }

  return new Transition(groups, this._parents, name, id);
}

selection.prototype.interrupt = selection_interrupt;
selection.prototype.transition = selection_transition;

var constant$1 = x => () => x;

function ZoomEvent(type, {
  sourceEvent,
  target,
  transform,
  dispatch
}) {
  Object.defineProperties(this, {
    type: {value: type, enumerable: true, configurable: true},
    sourceEvent: {value: sourceEvent, enumerable: true, configurable: true},
    target: {value: target, enumerable: true, configurable: true},
    transform: {value: transform, enumerable: true, configurable: true},
    _: {value: dispatch}
  });
}

function Transform(k, x, y) {
  this.k = k;
  this.x = x;
  this.y = y;
}

Transform.prototype = {
  constructor: Transform,
  scale: function(k) {
    return k === 1 ? this : new Transform(this.k * k, this.x, this.y);
  },
  translate: function(x, y) {
    return x === 0 & y === 0 ? this : new Transform(this.k, this.x + this.k * x, this.y + this.k * y);
  },
  apply: function(point) {
    return [point[0] * this.k + this.x, point[1] * this.k + this.y];
  },
  applyX: function(x) {
    return x * this.k + this.x;
  },
  applyY: function(y) {
    return y * this.k + this.y;
  },
  invert: function(location) {
    return [(location[0] - this.x) / this.k, (location[1] - this.y) / this.k];
  },
  invertX: function(x) {
    return (x - this.x) / this.k;
  },
  invertY: function(y) {
    return (y - this.y) / this.k;
  },
  rescaleX: function(x) {
    return x.copy().domain(x.range().map(this.invertX, this).map(x.invert, x));
  },
  rescaleY: function(y) {
    return y.copy().domain(y.range().map(this.invertY, this).map(y.invert, y));
  },
  toString: function() {
    return "translate(" + this.x + "," + this.y + ") scale(" + this.k + ")";
  }
};

var identity = new Transform(1, 0, 0);

Transform.prototype;

function nopropagation(event) {
  event.stopImmediatePropagation();
}

function noevent(event) {
  event.preventDefault();
  event.stopImmediatePropagation();
}

// Ignore right-click, since that should open the context menu.
// except for pinch-to-zoom, which is sent as a wheel+ctrlKey event
function defaultFilter(event) {
  return (!event.ctrlKey || event.type === 'wheel') && !event.button;
}

function defaultExtent() {
  var e = this;
  if (e instanceof SVGElement) {
    e = e.ownerSVGElement || e;
    if (e.hasAttribute("viewBox")) {
      e = e.viewBox.baseVal;
      return [[e.x, e.y], [e.x + e.width, e.y + e.height]];
    }
    return [[0, 0], [e.width.baseVal.value, e.height.baseVal.value]];
  }
  return [[0, 0], [e.clientWidth, e.clientHeight]];
}

function defaultTransform() {
  return this.__zoom || identity;
}

function defaultWheelDelta(event) {
  return -event.deltaY * (event.deltaMode === 1 ? 0.05 : event.deltaMode ? 1 : 0.002) * (event.ctrlKey ? 10 : 1);
}

function defaultTouchable() {
  return navigator.maxTouchPoints || ("ontouchstart" in this);
}

function defaultConstrain(transform, extent, translateExtent) {
  var dx0 = transform.invertX(extent[0][0]) - translateExtent[0][0],
      dx1 = transform.invertX(extent[1][0]) - translateExtent[1][0],
      dy0 = transform.invertY(extent[0][1]) - translateExtent[0][1],
      dy1 = transform.invertY(extent[1][1]) - translateExtent[1][1];
  return transform.translate(
    dx1 > dx0 ? (dx0 + dx1) / 2 : Math.min(0, dx0) || Math.max(0, dx1),
    dy1 > dy0 ? (dy0 + dy1) / 2 : Math.min(0, dy0) || Math.max(0, dy1)
  );
}

function d3zoom() {
  var filter = defaultFilter,
      extent = defaultExtent,
      constrain = defaultConstrain,
      wheelDelta = defaultWheelDelta,
      touchable = defaultTouchable,
      scaleExtent = [0, Infinity],
      translateExtent = [[-Infinity, -Infinity], [Infinity, Infinity]],
      duration = 250,
      interpolate = interpolateZoom,
      listeners = dispatch("start", "zoom", "end"),
      touchstarting,
      touchfirst,
      touchending,
      touchDelay = 500,
      wheelDelay = 150,
      clickDistance2 = 0,
      tapDistance = 10;

  function zoom(selection) {
    selection
        .property("__zoom", defaultTransform)
        .on("wheel.zoom", wheeled, {passive: false})
        .on("mousedown.zoom", mousedowned)
        .on("dblclick.zoom", dblclicked)
      .filter(touchable)
        .on("touchstart.zoom", touchstarted)
        .on("touchmove.zoom", touchmoved)
        .on("touchend.zoom touchcancel.zoom", touchended)
        .style("-webkit-tap-highlight-color", "rgba(0,0,0,0)");
  }

  zoom.transform = function(collection, transform, point, event) {
    var selection = collection.selection ? collection.selection() : collection;
    selection.property("__zoom", defaultTransform);
    if (collection !== selection) {
      schedule(collection, transform, point, event);
    } else {
      selection.interrupt().each(function() {
        gesture(this, arguments)
          .event(event)
          .start()
          .zoom(null, typeof transform === "function" ? transform.apply(this, arguments) : transform)
          .end();
      });
    }
  };

  zoom.scaleBy = function(selection, k, p, event) {
    zoom.scaleTo(selection, function() {
      var k0 = this.__zoom.k,
          k1 = typeof k === "function" ? k.apply(this, arguments) : k;
      return k0 * k1;
    }, p, event);
  };

  zoom.scaleTo = function(selection, k, p, event) {
    zoom.transform(selection, function() {
      var e = extent.apply(this, arguments),
          t0 = this.__zoom,
          p0 = p == null ? centroid(e) : typeof p === "function" ? p.apply(this, arguments) : p,
          p1 = t0.invert(p0),
          k1 = typeof k === "function" ? k.apply(this, arguments) : k;
      return constrain(translate(scale(t0, k1), p0, p1), e, translateExtent);
    }, p, event);
  };

  zoom.translateBy = function(selection, x, y, event) {
    zoom.transform(selection, function() {
      return constrain(this.__zoom.translate(
        typeof x === "function" ? x.apply(this, arguments) : x,
        typeof y === "function" ? y.apply(this, arguments) : y
      ), extent.apply(this, arguments), translateExtent);
    }, null, event);
  };

  zoom.translateTo = function(selection, x, y, p, event) {
    zoom.transform(selection, function() {
      var e = extent.apply(this, arguments),
          t = this.__zoom,
          p0 = p == null ? centroid(e) : typeof p === "function" ? p.apply(this, arguments) : p;
      return constrain(identity.translate(p0[0], p0[1]).scale(t.k).translate(
        typeof x === "function" ? -x.apply(this, arguments) : -x,
        typeof y === "function" ? -y.apply(this, arguments) : -y
      ), e, translateExtent);
    }, p, event);
  };

  function scale(transform, k) {
    k = Math.max(scaleExtent[0], Math.min(scaleExtent[1], k));
    return k === transform.k ? transform : new Transform(k, transform.x, transform.y);
  }

  function translate(transform, p0, p1) {
    var x = p0[0] - p1[0] * transform.k, y = p0[1] - p1[1] * transform.k;
    return x === transform.x && y === transform.y ? transform : new Transform(transform.k, x, y);
  }

  function centroid(extent) {
    return [(+extent[0][0] + +extent[1][0]) / 2, (+extent[0][1] + +extent[1][1]) / 2];
  }

  function schedule(transition, transform, point, event) {
    transition
        .on("start.zoom", function() { gesture(this, arguments).event(event).start(); })
        .on("interrupt.zoom end.zoom", function() { gesture(this, arguments).event(event).end(); })
        .tween("zoom", function() {
          var that = this,
              args = arguments,
              g = gesture(that, args).event(event),
              e = extent.apply(that, args),
              p = point == null ? centroid(e) : typeof point === "function" ? point.apply(that, args) : point,
              w = Math.max(e[1][0] - e[0][0], e[1][1] - e[0][1]),
              a = that.__zoom,
              b = typeof transform === "function" ? transform.apply(that, args) : transform,
              i = interpolate(a.invert(p).concat(w / a.k), b.invert(p).concat(w / b.k));
          return function(t) {
            if (t === 1) t = b; // Avoid rounding error on end.
            else { var l = i(t), k = w / l[2]; t = new Transform(k, p[0] - l[0] * k, p[1] - l[1] * k); }
            g.zoom(null, t);
          };
        });
  }

  function gesture(that, args, clean) {
    return (!clean && that.__zooming) || new Gesture(that, args);
  }

  function Gesture(that, args) {
    this.that = that;
    this.args = args;
    this.active = 0;
    this.sourceEvent = null;
    this.extent = extent.apply(that, args);
    this.taps = 0;
  }

  Gesture.prototype = {
    event: function(event) {
      if (event) this.sourceEvent = event;
      return this;
    },
    start: function() {
      if (++this.active === 1) {
        this.that.__zooming = this;
        this.emit("start");
      }
      return this;
    },
    zoom: function(key, transform) {
      if (this.mouse && key !== "mouse") this.mouse[1] = transform.invert(this.mouse[0]);
      if (this.touch0 && key !== "touch") this.touch0[1] = transform.invert(this.touch0[0]);
      if (this.touch1 && key !== "touch") this.touch1[1] = transform.invert(this.touch1[0]);
      this.that.__zoom = transform;
      this.emit("zoom");
      return this;
    },
    end: function() {
      if (--this.active === 0) {
        delete this.that.__zooming;
        this.emit("end");
      }
      return this;
    },
    emit: function(type) {
      var d = select(this.that).datum();
      listeners.call(
        type,
        this.that,
        new ZoomEvent(type, {
          sourceEvent: this.sourceEvent,
          target: zoom,
          type,
          transform: this.that.__zoom,
          dispatch: listeners
        }),
        d
      );
    }
  };

  function wheeled(event, ...args) {
    if (!filter.apply(this, arguments)) return;
    var g = gesture(this, args).event(event),
        t = this.__zoom,
        k = Math.max(scaleExtent[0], Math.min(scaleExtent[1], t.k * Math.pow(2, wheelDelta.apply(this, arguments)))),
        p = pointer(event);

    // If the mouse is in the same location as before, reuse it.
    // If there were recent wheel events, reset the wheel idle timeout.
    if (g.wheel) {
      if (g.mouse[0][0] !== p[0] || g.mouse[0][1] !== p[1]) {
        g.mouse[1] = t.invert(g.mouse[0] = p);
      }
      clearTimeout(g.wheel);
    }

    // If this wheel event won’t trigger a transform change, ignore it.
    else if (t.k === k) return;

    // Otherwise, capture the mouse point and location at the start.
    else {
      g.mouse = [p, t.invert(p)];
      interrupt(this);
      g.start();
    }

    noevent(event);
    g.wheel = setTimeout(wheelidled, wheelDelay);
    g.zoom("mouse", constrain(translate(scale(t, k), g.mouse[0], g.mouse[1]), g.extent, translateExtent));

    function wheelidled() {
      g.wheel = null;
      g.end();
    }
  }

  function mousedowned(event, ...args) {
    if (touchending || !filter.apply(this, arguments)) return;
    var currentTarget = event.currentTarget,
        g = gesture(this, args, true).event(event),
        v = select(event.view).on("mousemove.zoom", mousemoved, true).on("mouseup.zoom", mouseupped, true),
        p = pointer(event, currentTarget),
        x0 = event.clientX,
        y0 = event.clientY;

    dragDisable(event.view);
    nopropagation(event);
    g.mouse = [p, this.__zoom.invert(p)];
    interrupt(this);
    g.start();

    function mousemoved(event) {
      noevent(event);
      if (!g.moved) {
        var dx = event.clientX - x0, dy = event.clientY - y0;
        g.moved = dx * dx + dy * dy > clickDistance2;
      }
      g.event(event)
       .zoom("mouse", constrain(translate(g.that.__zoom, g.mouse[0] = pointer(event, currentTarget), g.mouse[1]), g.extent, translateExtent));
    }

    function mouseupped(event) {
      v.on("mousemove.zoom mouseup.zoom", null);
      yesdrag(event.view, g.moved);
      noevent(event);
      g.event(event).end();
    }
  }

  function dblclicked(event, ...args) {
    if (!filter.apply(this, arguments)) return;
    var t0 = this.__zoom,
        p0 = pointer(event.changedTouches ? event.changedTouches[0] : event, this),
        p1 = t0.invert(p0),
        k1 = t0.k * (event.shiftKey ? 0.5 : 2),
        t1 = constrain(translate(scale(t0, k1), p0, p1), extent.apply(this, args), translateExtent);

    noevent(event);
    if (duration > 0) select(this).transition().duration(duration).call(schedule, t1, p0, event);
    else select(this).call(zoom.transform, t1, p0, event);
  }

  function touchstarted(event, ...args) {
    if (!filter.apply(this, arguments)) return;
    var touches = event.touches,
        n = touches.length,
        g = gesture(this, args, event.changedTouches.length === n).event(event),
        started, i, t, p;

    nopropagation(event);
    for (i = 0; i < n; ++i) {
      t = touches[i], p = pointer(t, this);
      p = [p, this.__zoom.invert(p), t.identifier];
      if (!g.touch0) g.touch0 = p, started = true, g.taps = 1 + !!touchstarting;
      else if (!g.touch1 && g.touch0[2] !== p[2]) g.touch1 = p, g.taps = 0;
    }

    if (touchstarting) touchstarting = clearTimeout(touchstarting);

    if (started) {
      if (g.taps < 2) touchfirst = p[0], touchstarting = setTimeout(function() { touchstarting = null; }, touchDelay);
      interrupt(this);
      g.start();
    }
  }

  function touchmoved(event, ...args) {
    if (!this.__zooming) return;
    var g = gesture(this, args).event(event),
        touches = event.changedTouches,
        n = touches.length, i, t, p, l;

    noevent(event);
    for (i = 0; i < n; ++i) {
      t = touches[i], p = pointer(t, this);
      if (g.touch0 && g.touch0[2] === t.identifier) g.touch0[0] = p;
      else if (g.touch1 && g.touch1[2] === t.identifier) g.touch1[0] = p;
    }
    t = g.that.__zoom;
    if (g.touch1) {
      var p0 = g.touch0[0], l0 = g.touch0[1],
          p1 = g.touch1[0], l1 = g.touch1[1],
          dp = (dp = p1[0] - p0[0]) * dp + (dp = p1[1] - p0[1]) * dp,
          dl = (dl = l1[0] - l0[0]) * dl + (dl = l1[1] - l0[1]) * dl;
      t = scale(t, Math.sqrt(dp / dl));
      p = [(p0[0] + p1[0]) / 2, (p0[1] + p1[1]) / 2];
      l = [(l0[0] + l1[0]) / 2, (l0[1] + l1[1]) / 2];
    }
    else if (g.touch0) p = g.touch0[0], l = g.touch0[1];
    else return;

    g.zoom("touch", constrain(translate(t, p, l), g.extent, translateExtent));
  }

  function touchended(event, ...args) {
    if (!this.__zooming) return;
    var g = gesture(this, args).event(event),
        touches = event.changedTouches,
        n = touches.length, i, t;

    nopropagation(event);
    if (touchending) clearTimeout(touchending);
    touchending = setTimeout(function() { touchending = null; }, touchDelay);
    for (i = 0; i < n; ++i) {
      t = touches[i];
      if (g.touch0 && g.touch0[2] === t.identifier) delete g.touch0;
      else if (g.touch1 && g.touch1[2] === t.identifier) delete g.touch1;
    }
    if (g.touch1 && !g.touch0) g.touch0 = g.touch1, delete g.touch1;
    if (g.touch0) g.touch0[1] = this.__zoom.invert(g.touch0[0]);
    else {
      g.end();
      // If this was a dbltap, reroute to the (optional) dblclick.zoom handler.
      if (g.taps === 2) {
        t = pointer(t, this);
        if (Math.hypot(touchfirst[0] - t[0], touchfirst[1] - t[1]) < tapDistance) {
          var p = select(this).on("dblclick.zoom");
          if (p) p.apply(this, arguments);
        }
      }
    }
  }

  zoom.wheelDelta = function(_) {
    return arguments.length ? (wheelDelta = typeof _ === "function" ? _ : constant$1(+_), zoom) : wheelDelta;
  };

  zoom.filter = function(_) {
    return arguments.length ? (filter = typeof _ === "function" ? _ : constant$1(!!_), zoom) : filter;
  };

  zoom.touchable = function(_) {
    return arguments.length ? (touchable = typeof _ === "function" ? _ : constant$1(!!_), zoom) : touchable;
  };

  zoom.extent = function(_) {
    return arguments.length ? (extent = typeof _ === "function" ? _ : constant$1([[+_[0][0], +_[0][1]], [+_[1][0], +_[1][1]]]), zoom) : extent;
  };

  zoom.scaleExtent = function(_) {
    return arguments.length ? (scaleExtent[0] = +_[0], scaleExtent[1] = +_[1], zoom) : [scaleExtent[0], scaleExtent[1]];
  };

  zoom.translateExtent = function(_) {
    return arguments.length ? (translateExtent[0][0] = +_[0][0], translateExtent[1][0] = +_[1][0], translateExtent[0][1] = +_[0][1], translateExtent[1][1] = +_[1][1], zoom) : [[translateExtent[0][0], translateExtent[0][1]], [translateExtent[1][0], translateExtent[1][1]]];
  };

  zoom.constrain = function(_) {
    return arguments.length ? (constrain = _, zoom) : constrain;
  };

  zoom.duration = function(_) {
    return arguments.length ? (duration = +_, zoom) : duration;
  };

  zoom.interpolate = function(_) {
    return arguments.length ? (interpolate = _, zoom) : interpolate;
  };

  zoom.on = function() {
    var value = listeners.on.apply(listeners, arguments);
    return value === listeners ? zoom : value;
  };

  zoom.clickDistance = function(_) {
    return arguments.length ? (clickDistance2 = (_ = +_) * _, zoom) : Math.sqrt(clickDistance2);
  };

  zoom.tapDistance = function(_) {
    return arguments.length ? (tapDistance = +_, zoom) : tapDistance;
  };

  return zoom;
}

var has$1 = Object.prototype.hasOwnProperty;

function dequal(foo, bar) {
	var ctor, len;
	if (foo === bar) return true;

	if (foo && bar && (ctor=foo.constructor) === bar.constructor) {
		if (ctor === Date) return foo.getTime() === bar.getTime();
		if (ctor === RegExp) return foo.toString() === bar.toString();

		if (ctor === Array) {
			if ((len=foo.length) === bar.length) {
				while (len-- && dequal(foo[len], bar[len]));
			}
			return len === -1;
		}

		if (!ctor || typeof foo === 'object') {
			len = 0;
			for (ctor in foo) {
				if (has$1.call(foo, ctor) && ++len && !has$1.call(bar, ctor)) return false;
				if (!(ctor in bar) || !dequal(foo[ctor], bar[ctor])) return false;
			}
			return Object.keys(bar).length === len;
		}
	}

	return foo !== foo && bar !== bar;
}

function getDefaultExportFromCjs (x) {
	return x && x.__esModule && Object.prototype.hasOwnProperty.call(x, 'default') ? x['default'] : x;
}

function getAugmentedNamespace(n) {
  if (n.__esModule) return n;
  var f = n.default;
	if (typeof f == "function") {
		var a = function a () {
			if (this instanceof a) {
        return Reflect.construct(f, arguments, this.constructor);
			}
			return f.apply(this, arguments);
		};
		a.prototype = f.prototype;
  } else a = {};
  Object.defineProperty(a, '__esModule', {value: true});
	Object.keys(n).forEach(function (k) {
		var d = Object.getOwnPropertyDescriptor(n, k);
		Object.defineProperty(a, k, d.get ? d : {
			enumerable: true,
			get: function () {
				return n[k];
			}
		});
	});
	return a;
}

var clone$1 = {exports: {}};

clone$1.exports;

(function (module) {
	var clone = (function() {

	function _instanceof(obj, type) {
	  return type != null && obj instanceof type;
	}

	var nativeMap;
	try {
	  nativeMap = Map;
	} catch(_) {
	  // maybe a reference error because no `Map`. Give it a dummy value that no
	  // value will ever be an instanceof.
	  nativeMap = function() {};
	}

	var nativeSet;
	try {
	  nativeSet = Set;
	} catch(_) {
	  nativeSet = function() {};
	}

	var nativePromise;
	try {
	  nativePromise = Promise;
	} catch(_) {
	  nativePromise = function() {};
	}

	/**
	 * Clones (copies) an Object using deep copying.
	 *
	 * This function supports circular references by default, but if you are certain
	 * there are no circular references in your object, you can save some CPU time
	 * by calling clone(obj, false).
	 *
	 * Caution: if `circular` is false and `parent` contains circular references,
	 * your program may enter an infinite loop and crash.
	 *
	 * @param `parent` - the object to be cloned
	 * @param `circular` - set to true if the object to be cloned may contain
	 *    circular references. (optional - true by default)
	 * @param `depth` - set to a number if the object is only to be cloned to
	 *    a particular depth. (optional - defaults to Infinity)
	 * @param `prototype` - sets the prototype to be used when cloning an object.
	 *    (optional - defaults to parent prototype).
	 * @param `includeNonEnumerable` - set to true if the non-enumerable properties
	 *    should be cloned as well. Non-enumerable properties on the prototype
	 *    chain will be ignored. (optional - false by default)
	*/
	function clone(parent, circular, depth, prototype, includeNonEnumerable) {
	  if (typeof circular === 'object') {
	    depth = circular.depth;
	    prototype = circular.prototype;
	    includeNonEnumerable = circular.includeNonEnumerable;
	    circular = circular.circular;
	  }
	  // maintain two arrays for circular references, where corresponding parents
	  // and children have the same index
	  var allParents = [];
	  var allChildren = [];

	  var useBuffer = typeof Buffer != 'undefined';

	  if (typeof circular == 'undefined')
	    circular = true;

	  if (typeof depth == 'undefined')
	    depth = Infinity;

	  // recurse this function so we don't reset allParents and allChildren
	  function _clone(parent, depth) {
	    // cloning null always returns null
	    if (parent === null)
	      return null;

	    if (depth === 0)
	      return parent;

	    var child;
	    var proto;
	    if (typeof parent != 'object') {
	      return parent;
	    }

	    if (_instanceof(parent, nativeMap)) {
	      child = new nativeMap();
	    } else if (_instanceof(parent, nativeSet)) {
	      child = new nativeSet();
	    } else if (_instanceof(parent, nativePromise)) {
	      child = new nativePromise(function (resolve, reject) {
	        parent.then(function(value) {
	          resolve(_clone(value, depth - 1));
	        }, function(err) {
	          reject(_clone(err, depth - 1));
	        });
	      });
	    } else if (clone.__isArray(parent)) {
	      child = [];
	    } else if (clone.__isRegExp(parent)) {
	      child = new RegExp(parent.source, __getRegExpFlags(parent));
	      if (parent.lastIndex) child.lastIndex = parent.lastIndex;
	    } else if (clone.__isDate(parent)) {
	      child = new Date(parent.getTime());
	    } else if (useBuffer && Buffer.isBuffer(parent)) {
	      if (Buffer.allocUnsafe) {
	        // Node.js >= 4.5.0
	        child = Buffer.allocUnsafe(parent.length);
	      } else {
	        // Older Node.js versions
	        child = new Buffer(parent.length);
	      }
	      parent.copy(child);
	      return child;
	    } else if (_instanceof(parent, Error)) {
	      child = Object.create(parent);
	    } else {
	      if (typeof prototype == 'undefined') {
	        proto = Object.getPrototypeOf(parent);
	        child = Object.create(proto);
	      }
	      else {
	        child = Object.create(prototype);
	        proto = prototype;
	      }
	    }

	    if (circular) {
	      var index = allParents.indexOf(parent);

	      if (index != -1) {
	        return allChildren[index];
	      }
	      allParents.push(parent);
	      allChildren.push(child);
	    }

	    if (_instanceof(parent, nativeMap)) {
	      parent.forEach(function(value, key) {
	        var keyChild = _clone(key, depth - 1);
	        var valueChild = _clone(value, depth - 1);
	        child.set(keyChild, valueChild);
	      });
	    }
	    if (_instanceof(parent, nativeSet)) {
	      parent.forEach(function(value) {
	        var entryChild = _clone(value, depth - 1);
	        child.add(entryChild);
	      });
	    }

	    for (var i in parent) {
	      var attrs;
	      if (proto) {
	        attrs = Object.getOwnPropertyDescriptor(proto, i);
	      }

	      if (attrs && attrs.set == null) {
	        continue;
	      }
	      child[i] = _clone(parent[i], depth - 1);
	    }

	    if (Object.getOwnPropertySymbols) {
	      var symbols = Object.getOwnPropertySymbols(parent);
	      for (var i = 0; i < symbols.length; i++) {
	        // Don't need to worry about cloning a symbol because it is a primitive,
	        // like a number or string.
	        var symbol = symbols[i];
	        var descriptor = Object.getOwnPropertyDescriptor(parent, symbol);
	        if (descriptor && !descriptor.enumerable && !includeNonEnumerable) {
	          continue;
	        }
	        child[symbol] = _clone(parent[symbol], depth - 1);
	        if (!descriptor.enumerable) {
	          Object.defineProperty(child, symbol, {
	            enumerable: false
	          });
	        }
	      }
	    }

	    if (includeNonEnumerable) {
	      var allPropertyNames = Object.getOwnPropertyNames(parent);
	      for (var i = 0; i < allPropertyNames.length; i++) {
	        var propertyName = allPropertyNames[i];
	        var descriptor = Object.getOwnPropertyDescriptor(parent, propertyName);
	        if (descriptor && descriptor.enumerable) {
	          continue;
	        }
	        child[propertyName] = _clone(parent[propertyName], depth - 1);
	        Object.defineProperty(child, propertyName, {
	          enumerable: false
	        });
	      }
	    }

	    return child;
	  }

	  return _clone(parent, depth);
	}

	/**
	 * Simple flat clone using prototype, accepts only objects, usefull for property
	 * override on FLAT configuration object (no nested props).
	 *
	 * USE WITH CAUTION! This may not behave as you wish if you do not know how this
	 * works.
	 */
	clone.clonePrototype = function clonePrototype(parent) {
	  if (parent === null)
	    return null;

	  var c = function () {};
	  c.prototype = parent;
	  return new c();
	};

	// private utility functions

	function __objToStr(o) {
	  return Object.prototype.toString.call(o);
	}
	clone.__objToStr = __objToStr;

	function __isDate(o) {
	  return typeof o === 'object' && __objToStr(o) === '[object Date]';
	}
	clone.__isDate = __isDate;

	function __isArray(o) {
	  return typeof o === 'object' && __objToStr(o) === '[object Array]';
	}
	clone.__isArray = __isArray;

	function __isRegExp(o) {
	  return typeof o === 'object' && __objToStr(o) === '[object RegExp]';
	}
	clone.__isRegExp = __isRegExp;

	function __getRegExpFlags(re) {
	  var flags = '';
	  if (re.global) flags += 'g';
	  if (re.ignoreCase) flags += 'i';
	  if (re.multiline) flags += 'm';
	  return flags;
	}
	clone.__getRegExpFlags = __getRegExpFlags;

	return clone;
	})();

	if (module.exports) {
	  module.exports = clone;
	} 
} (clone$1));

var cloneExports = clone$1.exports;
var clone = /*@__PURE__*/getDefaultExportFromCjs(cloneExports);

// Unique ID creation requires a high quality random # generator. In the browser we therefore
// require the crypto API and do not support built-in fallback to lower quality random number
// generators (like Math.random()).
var getRandomValues;
var rnds8 = new Uint8Array(16);
function rng() {
  // lazy load so that environments that need to polyfill have a chance to do so
  if (!getRandomValues) {
    // getRandomValues needs to be invoked in a context where "this" is a Crypto implementation. Also,
    // find the complete implementation of crypto (msCrypto) on IE11.
    getRandomValues = typeof crypto !== 'undefined' && crypto.getRandomValues && crypto.getRandomValues.bind(crypto) || typeof msCrypto !== 'undefined' && typeof msCrypto.getRandomValues === 'function' && msCrypto.getRandomValues.bind(msCrypto);

    if (!getRandomValues) {
      throw new Error('crypto.getRandomValues() not supported. See https://github.com/uuidjs/uuid#getrandomvalues-not-supported');
    }
  }

  return getRandomValues(rnds8);
}

var REGEX = /^(?:[0-9a-f]{8}-[0-9a-f]{4}-[1-5][0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}|00000000-0000-0000-0000-000000000000)$/i;

function validate(uuid) {
  return typeof uuid === 'string' && REGEX.test(uuid);
}

/**
 * Convert array of 16 byte values to UUID string format of the form:
 * XXXXXXXX-XXXX-XXXX-XXXX-XXXXXXXXXXXX
 */

var byteToHex = [];

for (var i = 0; i < 256; ++i) {
  byteToHex.push((i + 0x100).toString(16).substr(1));
}

function stringify(arr) {
  var offset = arguments.length > 1 && arguments[1] !== undefined ? arguments[1] : 0;
  // Note: Be careful editing this code!  It's been tuned for performance
  // and works in ways you may not expect. See https://github.com/uuidjs/uuid/pull/434
  var uuid = (byteToHex[arr[offset + 0]] + byteToHex[arr[offset + 1]] + byteToHex[arr[offset + 2]] + byteToHex[arr[offset + 3]] + '-' + byteToHex[arr[offset + 4]] + byteToHex[arr[offset + 5]] + '-' + byteToHex[arr[offset + 6]] + byteToHex[arr[offset + 7]] + '-' + byteToHex[arr[offset + 8]] + byteToHex[arr[offset + 9]] + '-' + byteToHex[arr[offset + 10]] + byteToHex[arr[offset + 11]] + byteToHex[arr[offset + 12]] + byteToHex[arr[offset + 13]] + byteToHex[arr[offset + 14]] + byteToHex[arr[offset + 15]]).toLowerCase(); // Consistency check for valid UUID.  If this throws, it's likely due to one
  // of the following:
  // - One or more input array values don't map to a hex octet (leading to
  // "undefined" in the uuid)
  // - Invalid input values for the RFC `version` or `variant` fields

  if (!validate(uuid)) {
    throw TypeError('Stringified UUID is invalid');
  }

  return uuid;
}

function v4(options, buf, offset) {
  options = options || {};
  var rnds = options.random || (options.rng || rng)(); // Per 4.4, set bits for version and `clock_seq_hi_and_reserved`

  rnds[6] = rnds[6] & 0x0f | 0x40;
  rnds[8] = rnds[8] & 0x3f | 0x80; // Copy bytes to buffer, if provided

  if (buf) {
    offset = offset || 0;

    for (var i = 0; i < 16; ++i) {
      buf[offset + i] = rnds[i];
    }

    return buf;
  }

  return stringify(rnds);
}

var CSSTransitionGroup = {exports: {}};

var propTypes = {exports: {}};

var reactIs = {exports: {}};

var reactIs_development = {};

/** @license React v16.13.1
 * react-is.development.js
 *
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

var hasRequiredReactIs_development;

function requireReactIs_development () {
	if (hasRequiredReactIs_development) return reactIs_development;
	hasRequiredReactIs_development = 1;



	{
	  (function() {

	// The Symbol used to tag the ReactElement-like types. If there is no native Symbol
	// nor polyfill, then a plain number is used for performance.
	var hasSymbol = typeof Symbol === 'function' && Symbol.for;
	var REACT_ELEMENT_TYPE = hasSymbol ? Symbol.for('react.element') : 0xeac7;
	var REACT_PORTAL_TYPE = hasSymbol ? Symbol.for('react.portal') : 0xeaca;
	var REACT_FRAGMENT_TYPE = hasSymbol ? Symbol.for('react.fragment') : 0xeacb;
	var REACT_STRICT_MODE_TYPE = hasSymbol ? Symbol.for('react.strict_mode') : 0xeacc;
	var REACT_PROFILER_TYPE = hasSymbol ? Symbol.for('react.profiler') : 0xead2;
	var REACT_PROVIDER_TYPE = hasSymbol ? Symbol.for('react.provider') : 0xeacd;
	var REACT_CONTEXT_TYPE = hasSymbol ? Symbol.for('react.context') : 0xeace; // TODO: We don't use AsyncMode or ConcurrentMode anymore. They were temporary
	// (unstable) APIs that have been removed. Can we remove the symbols?

	var REACT_ASYNC_MODE_TYPE = hasSymbol ? Symbol.for('react.async_mode') : 0xeacf;
	var REACT_CONCURRENT_MODE_TYPE = hasSymbol ? Symbol.for('react.concurrent_mode') : 0xeacf;
	var REACT_FORWARD_REF_TYPE = hasSymbol ? Symbol.for('react.forward_ref') : 0xead0;
	var REACT_SUSPENSE_TYPE = hasSymbol ? Symbol.for('react.suspense') : 0xead1;
	var REACT_SUSPENSE_LIST_TYPE = hasSymbol ? Symbol.for('react.suspense_list') : 0xead8;
	var REACT_MEMO_TYPE = hasSymbol ? Symbol.for('react.memo') : 0xead3;
	var REACT_LAZY_TYPE = hasSymbol ? Symbol.for('react.lazy') : 0xead4;
	var REACT_BLOCK_TYPE = hasSymbol ? Symbol.for('react.block') : 0xead9;
	var REACT_FUNDAMENTAL_TYPE = hasSymbol ? Symbol.for('react.fundamental') : 0xead5;
	var REACT_RESPONDER_TYPE = hasSymbol ? Symbol.for('react.responder') : 0xead6;
	var REACT_SCOPE_TYPE = hasSymbol ? Symbol.for('react.scope') : 0xead7;

	function isValidElementType(type) {
	  return typeof type === 'string' || typeof type === 'function' || // Note: its typeof might be other than 'symbol' or 'number' if it's a polyfill.
	  type === REACT_FRAGMENT_TYPE || type === REACT_CONCURRENT_MODE_TYPE || type === REACT_PROFILER_TYPE || type === REACT_STRICT_MODE_TYPE || type === REACT_SUSPENSE_TYPE || type === REACT_SUSPENSE_LIST_TYPE || typeof type === 'object' && type !== null && (type.$$typeof === REACT_LAZY_TYPE || type.$$typeof === REACT_MEMO_TYPE || type.$$typeof === REACT_PROVIDER_TYPE || type.$$typeof === REACT_CONTEXT_TYPE || type.$$typeof === REACT_FORWARD_REF_TYPE || type.$$typeof === REACT_FUNDAMENTAL_TYPE || type.$$typeof === REACT_RESPONDER_TYPE || type.$$typeof === REACT_SCOPE_TYPE || type.$$typeof === REACT_BLOCK_TYPE);
	}

	function typeOf(object) {
	  if (typeof object === 'object' && object !== null) {
	    var $$typeof = object.$$typeof;

	    switch ($$typeof) {
	      case REACT_ELEMENT_TYPE:
	        var type = object.type;

	        switch (type) {
	          case REACT_ASYNC_MODE_TYPE:
	          case REACT_CONCURRENT_MODE_TYPE:
	          case REACT_FRAGMENT_TYPE:
	          case REACT_PROFILER_TYPE:
	          case REACT_STRICT_MODE_TYPE:
	          case REACT_SUSPENSE_TYPE:
	            return type;

	          default:
	            var $$typeofType = type && type.$$typeof;

	            switch ($$typeofType) {
	              case REACT_CONTEXT_TYPE:
	              case REACT_FORWARD_REF_TYPE:
	              case REACT_LAZY_TYPE:
	              case REACT_MEMO_TYPE:
	              case REACT_PROVIDER_TYPE:
	                return $$typeofType;

	              default:
	                return $$typeof;
	            }

	        }

	      case REACT_PORTAL_TYPE:
	        return $$typeof;
	    }
	  }

	  return undefined;
	} // AsyncMode is deprecated along with isAsyncMode

	var AsyncMode = REACT_ASYNC_MODE_TYPE;
	var ConcurrentMode = REACT_CONCURRENT_MODE_TYPE;
	var ContextConsumer = REACT_CONTEXT_TYPE;
	var ContextProvider = REACT_PROVIDER_TYPE;
	var Element = REACT_ELEMENT_TYPE;
	var ForwardRef = REACT_FORWARD_REF_TYPE;
	var Fragment = REACT_FRAGMENT_TYPE;
	var Lazy = REACT_LAZY_TYPE;
	var Memo = REACT_MEMO_TYPE;
	var Portal = REACT_PORTAL_TYPE;
	var Profiler = REACT_PROFILER_TYPE;
	var StrictMode = REACT_STRICT_MODE_TYPE;
	var Suspense = REACT_SUSPENSE_TYPE;
	var hasWarnedAboutDeprecatedIsAsyncMode = false; // AsyncMode should be deprecated

	function isAsyncMode(object) {
	  {
	    if (!hasWarnedAboutDeprecatedIsAsyncMode) {
	      hasWarnedAboutDeprecatedIsAsyncMode = true; // Using console['warn'] to evade Babel and ESLint

	      console['warn']('The ReactIs.isAsyncMode() alias has been deprecated, ' + 'and will be removed in React 17+. Update your code to use ' + 'ReactIs.isConcurrentMode() instead. It has the exact same API.');
	    }
	  }

	  return isConcurrentMode(object) || typeOf(object) === REACT_ASYNC_MODE_TYPE;
	}
	function isConcurrentMode(object) {
	  return typeOf(object) === REACT_CONCURRENT_MODE_TYPE;
	}
	function isContextConsumer(object) {
	  return typeOf(object) === REACT_CONTEXT_TYPE;
	}
	function isContextProvider(object) {
	  return typeOf(object) === REACT_PROVIDER_TYPE;
	}
	function isElement(object) {
	  return typeof object === 'object' && object !== null && object.$$typeof === REACT_ELEMENT_TYPE;
	}
	function isForwardRef(object) {
	  return typeOf(object) === REACT_FORWARD_REF_TYPE;
	}
	function isFragment(object) {
	  return typeOf(object) === REACT_FRAGMENT_TYPE;
	}
	function isLazy(object) {
	  return typeOf(object) === REACT_LAZY_TYPE;
	}
	function isMemo(object) {
	  return typeOf(object) === REACT_MEMO_TYPE;
	}
	function isPortal(object) {
	  return typeOf(object) === REACT_PORTAL_TYPE;
	}
	function isProfiler(object) {
	  return typeOf(object) === REACT_PROFILER_TYPE;
	}
	function isStrictMode(object) {
	  return typeOf(object) === REACT_STRICT_MODE_TYPE;
	}
	function isSuspense(object) {
	  return typeOf(object) === REACT_SUSPENSE_TYPE;
	}

	reactIs_development.AsyncMode = AsyncMode;
	reactIs_development.ConcurrentMode = ConcurrentMode;
	reactIs_development.ContextConsumer = ContextConsumer;
	reactIs_development.ContextProvider = ContextProvider;
	reactIs_development.Element = Element;
	reactIs_development.ForwardRef = ForwardRef;
	reactIs_development.Fragment = Fragment;
	reactIs_development.Lazy = Lazy;
	reactIs_development.Memo = Memo;
	reactIs_development.Portal = Portal;
	reactIs_development.Profiler = Profiler;
	reactIs_development.StrictMode = StrictMode;
	reactIs_development.Suspense = Suspense;
	reactIs_development.isAsyncMode = isAsyncMode;
	reactIs_development.isConcurrentMode = isConcurrentMode;
	reactIs_development.isContextConsumer = isContextConsumer;
	reactIs_development.isContextProvider = isContextProvider;
	reactIs_development.isElement = isElement;
	reactIs_development.isForwardRef = isForwardRef;
	reactIs_development.isFragment = isFragment;
	reactIs_development.isLazy = isLazy;
	reactIs_development.isMemo = isMemo;
	reactIs_development.isPortal = isPortal;
	reactIs_development.isProfiler = isProfiler;
	reactIs_development.isStrictMode = isStrictMode;
	reactIs_development.isSuspense = isSuspense;
	reactIs_development.isValidElementType = isValidElementType;
	reactIs_development.typeOf = typeOf;
	  })();
	}
	return reactIs_development;
}

var hasRequiredReactIs;

function requireReactIs () {
	if (hasRequiredReactIs) return reactIs.exports;
	hasRequiredReactIs = 1;

	{
	  reactIs.exports = requireReactIs_development();
	}
	return reactIs.exports;
}

/*
object-assign
(c) Sindre Sorhus
@license MIT
*/

var objectAssign;
var hasRequiredObjectAssign;

function requireObjectAssign () {
	if (hasRequiredObjectAssign) return objectAssign;
	hasRequiredObjectAssign = 1;
	/* eslint-disable no-unused-vars */
	var getOwnPropertySymbols = Object.getOwnPropertySymbols;
	var hasOwnProperty = Object.prototype.hasOwnProperty;
	var propIsEnumerable = Object.prototype.propertyIsEnumerable;

	function toObject(val) {
		if (val === null || val === undefined) {
			throw new TypeError('Object.assign cannot be called with null or undefined');
		}

		return Object(val);
	}

	function shouldUseNative() {
		try {
			if (!Object.assign) {
				return false;
			}

			// Detect buggy property enumeration order in older V8 versions.

			// https://bugs.chromium.org/p/v8/issues/detail?id=4118
			var test1 = new String('abc');  // eslint-disable-line no-new-wrappers
			test1[5] = 'de';
			if (Object.getOwnPropertyNames(test1)[0] === '5') {
				return false;
			}

			// https://bugs.chromium.org/p/v8/issues/detail?id=3056
			var test2 = {};
			for (var i = 0; i < 10; i++) {
				test2['_' + String.fromCharCode(i)] = i;
			}
			var order2 = Object.getOwnPropertyNames(test2).map(function (n) {
				return test2[n];
			});
			if (order2.join('') !== '0123456789') {
				return false;
			}

			// https://bugs.chromium.org/p/v8/issues/detail?id=3056
			var test3 = {};
			'abcdefghijklmnopqrst'.split('').forEach(function (letter) {
				test3[letter] = letter;
			});
			if (Object.keys(Object.assign({}, test3)).join('') !==
					'abcdefghijklmnopqrst') {
				return false;
			}

			return true;
		} catch (err) {
			// We don't expect any of the above to throw, but better to be safe.
			return false;
		}
	}

	objectAssign = shouldUseNative() ? Object.assign : function (target, source) {
		var from;
		var to = toObject(target);
		var symbols;

		for (var s = 1; s < arguments.length; s++) {
			from = Object(arguments[s]);

			for (var key in from) {
				if (hasOwnProperty.call(from, key)) {
					to[key] = from[key];
				}
			}

			if (getOwnPropertySymbols) {
				symbols = getOwnPropertySymbols(from);
				for (var i = 0; i < symbols.length; i++) {
					if (propIsEnumerable.call(from, symbols[i])) {
						to[symbols[i]] = from[symbols[i]];
					}
				}
			}
		}

		return to;
	};
	return objectAssign;
}

/**
 * Copyright (c) 2013-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

var ReactPropTypesSecret_1;
var hasRequiredReactPropTypesSecret;

function requireReactPropTypesSecret () {
	if (hasRequiredReactPropTypesSecret) return ReactPropTypesSecret_1;
	hasRequiredReactPropTypesSecret = 1;

	var ReactPropTypesSecret = 'SECRET_DO_NOT_PASS_THIS_OR_YOU_WILL_BE_FIRED';

	ReactPropTypesSecret_1 = ReactPropTypesSecret;
	return ReactPropTypesSecret_1;
}

var has;
var hasRequiredHas;

function requireHas () {
	if (hasRequiredHas) return has;
	hasRequiredHas = 1;
	has = Function.call.bind(Object.prototype.hasOwnProperty);
	return has;
}

/**
 * Copyright (c) 2013-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

var checkPropTypes_1;
var hasRequiredCheckPropTypes;

function requireCheckPropTypes () {
	if (hasRequiredCheckPropTypes) return checkPropTypes_1;
	hasRequiredCheckPropTypes = 1;

	var printWarning = function() {};

	{
	  var ReactPropTypesSecret = requireReactPropTypesSecret();
	  var loggedTypeFailures = {};
	  var has = requireHas();

	  printWarning = function(text) {
	    var message = 'Warning: ' + text;
	    if (typeof console !== 'undefined') {
	      console.error(message);
	    }
	    try {
	      // --- Welcome to debugging React ---
	      // This error was thrown as a convenience so that you can use this stack
	      // to find the callsite that caused this warning to fire.
	      throw new Error(message);
	    } catch (x) { /**/ }
	  };
	}

	/**
	 * Assert that the values match with the type specs.
	 * Error messages are memorized and will only be shown once.
	 *
	 * @param {object} typeSpecs Map of name to a ReactPropType
	 * @param {object} values Runtime values that need to be type-checked
	 * @param {string} location e.g. "prop", "context", "child context"
	 * @param {string} componentName Name of the component for error messages.
	 * @param {?Function} getStack Returns the component stack.
	 * @private
	 */
	function checkPropTypes(typeSpecs, values, location, componentName, getStack) {
	  {
	    for (var typeSpecName in typeSpecs) {
	      if (has(typeSpecs, typeSpecName)) {
	        var error;
	        // Prop type validation may throw. In case they do, we don't want to
	        // fail the render phase where it didn't fail before. So we log it.
	        // After these have been cleaned up, we'll let them throw.
	        try {
	          // This is intentionally an invariant that gets caught. It's the same
	          // behavior as without this statement except with a better message.
	          if (typeof typeSpecs[typeSpecName] !== 'function') {
	            var err = Error(
	              (componentName || 'React class') + ': ' + location + ' type `' + typeSpecName + '` is invalid; ' +
	              'it must be a function, usually from the `prop-types` package, but received `' + typeof typeSpecs[typeSpecName] + '`.' +
	              'This often happens because of typos such as `PropTypes.function` instead of `PropTypes.func`.'
	            );
	            err.name = 'Invariant Violation';
	            throw err;
	          }
	          error = typeSpecs[typeSpecName](values, typeSpecName, componentName, location, null, ReactPropTypesSecret);
	        } catch (ex) {
	          error = ex;
	        }
	        if (error && !(error instanceof Error)) {
	          printWarning(
	            (componentName || 'React class') + ': type specification of ' +
	            location + ' `' + typeSpecName + '` is invalid; the type checker ' +
	            'function must return `null` or an `Error` but returned a ' + typeof error + '. ' +
	            'You may have forgotten to pass an argument to the type checker ' +
	            'creator (arrayOf, instanceOf, objectOf, oneOf, oneOfType, and ' +
	            'shape all require an argument).'
	          );
	        }
	        if (error instanceof Error && !(error.message in loggedTypeFailures)) {
	          // Only monitor this failure once because there tends to be a lot of the
	          // same error.
	          loggedTypeFailures[error.message] = true;

	          var stack = getStack ? getStack() : '';

	          printWarning(
	            'Failed ' + location + ' type: ' + error.message + (stack != null ? stack : '')
	          );
	        }
	      }
	    }
	  }
	}

	/**
	 * Resets warning cache when testing.
	 *
	 * @private
	 */
	checkPropTypes.resetWarningCache = function() {
	  {
	    loggedTypeFailures = {};
	  }
	};

	checkPropTypes_1 = checkPropTypes;
	return checkPropTypes_1;
}

/**
 * Copyright (c) 2013-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

var factoryWithTypeCheckers;
var hasRequiredFactoryWithTypeCheckers;

function requireFactoryWithTypeCheckers () {
	if (hasRequiredFactoryWithTypeCheckers) return factoryWithTypeCheckers;
	hasRequiredFactoryWithTypeCheckers = 1;

	var ReactIs = requireReactIs();
	var assign = requireObjectAssign();

	var ReactPropTypesSecret = requireReactPropTypesSecret();
	var has = requireHas();
	var checkPropTypes = requireCheckPropTypes();

	var printWarning = function() {};

	{
	  printWarning = function(text) {
	    var message = 'Warning: ' + text;
	    if (typeof console !== 'undefined') {
	      console.error(message);
	    }
	    try {
	      // --- Welcome to debugging React ---
	      // This error was thrown as a convenience so that you can use this stack
	      // to find the callsite that caused this warning to fire.
	      throw new Error(message);
	    } catch (x) {}
	  };
	}

	function emptyFunctionThatReturnsNull() {
	  return null;
	}

	factoryWithTypeCheckers = function(isValidElement, throwOnDirectAccess) {
	  /* global Symbol */
	  var ITERATOR_SYMBOL = typeof Symbol === 'function' && Symbol.iterator;
	  var FAUX_ITERATOR_SYMBOL = '@@iterator'; // Before Symbol spec.

	  /**
	   * Returns the iterator method function contained on the iterable object.
	   *
	   * Be sure to invoke the function with the iterable as context:
	   *
	   *     var iteratorFn = getIteratorFn(myIterable);
	   *     if (iteratorFn) {
	   *       var iterator = iteratorFn.call(myIterable);
	   *       ...
	   *     }
	   *
	   * @param {?object} maybeIterable
	   * @return {?function}
	   */
	  function getIteratorFn(maybeIterable) {
	    var iteratorFn = maybeIterable && (ITERATOR_SYMBOL && maybeIterable[ITERATOR_SYMBOL] || maybeIterable[FAUX_ITERATOR_SYMBOL]);
	    if (typeof iteratorFn === 'function') {
	      return iteratorFn;
	    }
	  }

	  /**
	   * Collection of methods that allow declaration and validation of props that are
	   * supplied to React components. Example usage:
	   *
	   *   var Props = require('ReactPropTypes');
	   *   var MyArticle = React.createClass({
	   *     propTypes: {
	   *       // An optional string prop named "description".
	   *       description: Props.string,
	   *
	   *       // A required enum prop named "category".
	   *       category: Props.oneOf(['News','Photos']).isRequired,
	   *
	   *       // A prop named "dialog" that requires an instance of Dialog.
	   *       dialog: Props.instanceOf(Dialog).isRequired
	   *     },
	   *     render: function() { ... }
	   *   });
	   *
	   * A more formal specification of how these methods are used:
	   *
	   *   type := array|bool|func|object|number|string|oneOf([...])|instanceOf(...)
	   *   decl := ReactPropTypes.{type}(.isRequired)?
	   *
	   * Each and every declaration produces a function with the same signature. This
	   * allows the creation of custom validation functions. For example:
	   *
	   *  var MyLink = React.createClass({
	   *    propTypes: {
	   *      // An optional string or URI prop named "href".
	   *      href: function(props, propName, componentName) {
	   *        var propValue = props[propName];
	   *        if (propValue != null && typeof propValue !== 'string' &&
	   *            !(propValue instanceof URI)) {
	   *          return new Error(
	   *            'Expected a string or an URI for ' + propName + ' in ' +
	   *            componentName
	   *          );
	   *        }
	   *      }
	   *    },
	   *    render: function() {...}
	   *  });
	   *
	   * @internal
	   */

	  var ANONYMOUS = '<<anonymous>>';

	  // Important!
	  // Keep this list in sync with production version in `./factoryWithThrowingShims.js`.
	  var ReactPropTypes = {
	    array: createPrimitiveTypeChecker('array'),
	    bigint: createPrimitiveTypeChecker('bigint'),
	    bool: createPrimitiveTypeChecker('boolean'),
	    func: createPrimitiveTypeChecker('function'),
	    number: createPrimitiveTypeChecker('number'),
	    object: createPrimitiveTypeChecker('object'),
	    string: createPrimitiveTypeChecker('string'),
	    symbol: createPrimitiveTypeChecker('symbol'),

	    any: createAnyTypeChecker(),
	    arrayOf: createArrayOfTypeChecker,
	    element: createElementTypeChecker(),
	    elementType: createElementTypeTypeChecker(),
	    instanceOf: createInstanceTypeChecker,
	    node: createNodeChecker(),
	    objectOf: createObjectOfTypeChecker,
	    oneOf: createEnumTypeChecker,
	    oneOfType: createUnionTypeChecker,
	    shape: createShapeTypeChecker,
	    exact: createStrictShapeTypeChecker,
	  };

	  /**
	   * inlined Object.is polyfill to avoid requiring consumers ship their own
	   * https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Object/is
	   */
	  /*eslint-disable no-self-compare*/
	  function is(x, y) {
	    // SameValue algorithm
	    if (x === y) {
	      // Steps 1-5, 7-10
	      // Steps 6.b-6.e: +0 != -0
	      return x !== 0 || 1 / x === 1 / y;
	    } else {
	      // Step 6.a: NaN == NaN
	      return x !== x && y !== y;
	    }
	  }
	  /*eslint-enable no-self-compare*/

	  /**
	   * We use an Error-like object for backward compatibility as people may call
	   * PropTypes directly and inspect their output. However, we don't use real
	   * Errors anymore. We don't inspect their stack anyway, and creating them
	   * is prohibitively expensive if they are created too often, such as what
	   * happens in oneOfType() for any type before the one that matched.
	   */
	  function PropTypeError(message, data) {
	    this.message = message;
	    this.data = data && typeof data === 'object' ? data: {};
	    this.stack = '';
	  }
	  // Make `instanceof Error` still work for returned errors.
	  PropTypeError.prototype = Error.prototype;

	  function createChainableTypeChecker(validate) {
	    {
	      var manualPropTypeCallCache = {};
	      var manualPropTypeWarningCount = 0;
	    }
	    function checkType(isRequired, props, propName, componentName, location, propFullName, secret) {
	      componentName = componentName || ANONYMOUS;
	      propFullName = propFullName || propName;

	      if (secret !== ReactPropTypesSecret) {
	        if (throwOnDirectAccess) {
	          // New behavior only for users of `prop-types` package
	          var err = new Error(
	            'Calling PropTypes validators directly is not supported by the `prop-types` package. ' +
	            'Use `PropTypes.checkPropTypes()` to call them. ' +
	            'Read more at http://fb.me/use-check-prop-types'
	          );
	          err.name = 'Invariant Violation';
	          throw err;
	        } else if (typeof console !== 'undefined') {
	          // Old behavior for people using React.PropTypes
	          var cacheKey = componentName + ':' + propName;
	          if (
	            !manualPropTypeCallCache[cacheKey] &&
	            // Avoid spamming the console because they are often not actionable except for lib authors
	            manualPropTypeWarningCount < 3
	          ) {
	            printWarning(
	              'You are manually calling a React.PropTypes validation ' +
	              'function for the `' + propFullName + '` prop on `' + componentName + '`. This is deprecated ' +
	              'and will throw in the standalone `prop-types` package. ' +
	              'You may be seeing this warning due to a third-party PropTypes ' +
	              'library. See https://fb.me/react-warning-dont-call-proptypes ' + 'for details.'
	            );
	            manualPropTypeCallCache[cacheKey] = true;
	            manualPropTypeWarningCount++;
	          }
	        }
	      }
	      if (props[propName] == null) {
	        if (isRequired) {
	          if (props[propName] === null) {
	            return new PropTypeError('The ' + location + ' `' + propFullName + '` is marked as required ' + ('in `' + componentName + '`, but its value is `null`.'));
	          }
	          return new PropTypeError('The ' + location + ' `' + propFullName + '` is marked as required in ' + ('`' + componentName + '`, but its value is `undefined`.'));
	        }
	        return null;
	      } else {
	        return validate(props, propName, componentName, location, propFullName);
	      }
	    }

	    var chainedCheckType = checkType.bind(null, false);
	    chainedCheckType.isRequired = checkType.bind(null, true);

	    return chainedCheckType;
	  }

	  function createPrimitiveTypeChecker(expectedType) {
	    function validate(props, propName, componentName, location, propFullName, secret) {
	      var propValue = props[propName];
	      var propType = getPropType(propValue);
	      if (propType !== expectedType) {
	        // `propValue` being instance of, say, date/regexp, pass the 'object'
	        // check, but we can offer a more precise error message here rather than
	        // 'of type `object`'.
	        var preciseType = getPreciseType(propValue);

	        return new PropTypeError(
	          'Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + preciseType + '` supplied to `' + componentName + '`, expected ') + ('`' + expectedType + '`.'),
	          {expectedType: expectedType}
	        );
	      }
	      return null;
	    }
	    return createChainableTypeChecker(validate);
	  }

	  function createAnyTypeChecker() {
	    return createChainableTypeChecker(emptyFunctionThatReturnsNull);
	  }

	  function createArrayOfTypeChecker(typeChecker) {
	    function validate(props, propName, componentName, location, propFullName) {
	      if (typeof typeChecker !== 'function') {
	        return new PropTypeError('Property `' + propFullName + '` of component `' + componentName + '` has invalid PropType notation inside arrayOf.');
	      }
	      var propValue = props[propName];
	      if (!Array.isArray(propValue)) {
	        var propType = getPropType(propValue);
	        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected an array.'));
	      }
	      for (var i = 0; i < propValue.length; i++) {
	        var error = typeChecker(propValue, i, componentName, location, propFullName + '[' + i + ']', ReactPropTypesSecret);
	        if (error instanceof Error) {
	          return error;
	        }
	      }
	      return null;
	    }
	    return createChainableTypeChecker(validate);
	  }

	  function createElementTypeChecker() {
	    function validate(props, propName, componentName, location, propFullName) {
	      var propValue = props[propName];
	      if (!isValidElement(propValue)) {
	        var propType = getPropType(propValue);
	        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected a single ReactElement.'));
	      }
	      return null;
	    }
	    return createChainableTypeChecker(validate);
	  }

	  function createElementTypeTypeChecker() {
	    function validate(props, propName, componentName, location, propFullName) {
	      var propValue = props[propName];
	      if (!ReactIs.isValidElementType(propValue)) {
	        var propType = getPropType(propValue);
	        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected a single ReactElement type.'));
	      }
	      return null;
	    }
	    return createChainableTypeChecker(validate);
	  }

	  function createInstanceTypeChecker(expectedClass) {
	    function validate(props, propName, componentName, location, propFullName) {
	      if (!(props[propName] instanceof expectedClass)) {
	        var expectedClassName = expectedClass.name || ANONYMOUS;
	        var actualClassName = getClassName(props[propName]);
	        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + actualClassName + '` supplied to `' + componentName + '`, expected ') + ('instance of `' + expectedClassName + '`.'));
	      }
	      return null;
	    }
	    return createChainableTypeChecker(validate);
	  }

	  function createEnumTypeChecker(expectedValues) {
	    if (!Array.isArray(expectedValues)) {
	      {
	        if (arguments.length > 1) {
	          printWarning(
	            'Invalid arguments supplied to oneOf, expected an array, got ' + arguments.length + ' arguments. ' +
	            'A common mistake is to write oneOf(x, y, z) instead of oneOf([x, y, z]).'
	          );
	        } else {
	          printWarning('Invalid argument supplied to oneOf, expected an array.');
	        }
	      }
	      return emptyFunctionThatReturnsNull;
	    }

	    function validate(props, propName, componentName, location, propFullName) {
	      var propValue = props[propName];
	      for (var i = 0; i < expectedValues.length; i++) {
	        if (is(propValue, expectedValues[i])) {
	          return null;
	        }
	      }

	      var valuesString = JSON.stringify(expectedValues, function replacer(key, value) {
	        var type = getPreciseType(value);
	        if (type === 'symbol') {
	          return String(value);
	        }
	        return value;
	      });
	      return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of value `' + String(propValue) + '` ' + ('supplied to `' + componentName + '`, expected one of ' + valuesString + '.'));
	    }
	    return createChainableTypeChecker(validate);
	  }

	  function createObjectOfTypeChecker(typeChecker) {
	    function validate(props, propName, componentName, location, propFullName) {
	      if (typeof typeChecker !== 'function') {
	        return new PropTypeError('Property `' + propFullName + '` of component `' + componentName + '` has invalid PropType notation inside objectOf.');
	      }
	      var propValue = props[propName];
	      var propType = getPropType(propValue);
	      if (propType !== 'object') {
	        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected an object.'));
	      }
	      for (var key in propValue) {
	        if (has(propValue, key)) {
	          var error = typeChecker(propValue, key, componentName, location, propFullName + '.' + key, ReactPropTypesSecret);
	          if (error instanceof Error) {
	            return error;
	          }
	        }
	      }
	      return null;
	    }
	    return createChainableTypeChecker(validate);
	  }

	  function createUnionTypeChecker(arrayOfTypeCheckers) {
	    if (!Array.isArray(arrayOfTypeCheckers)) {
	      printWarning('Invalid argument supplied to oneOfType, expected an instance of array.') ;
	      return emptyFunctionThatReturnsNull;
	    }

	    for (var i = 0; i < arrayOfTypeCheckers.length; i++) {
	      var checker = arrayOfTypeCheckers[i];
	      if (typeof checker !== 'function') {
	        printWarning(
	          'Invalid argument supplied to oneOfType. Expected an array of check functions, but ' +
	          'received ' + getPostfixForTypeWarning(checker) + ' at index ' + i + '.'
	        );
	        return emptyFunctionThatReturnsNull;
	      }
	    }

	    function validate(props, propName, componentName, location, propFullName) {
	      var expectedTypes = [];
	      for (var i = 0; i < arrayOfTypeCheckers.length; i++) {
	        var checker = arrayOfTypeCheckers[i];
	        var checkerResult = checker(props, propName, componentName, location, propFullName, ReactPropTypesSecret);
	        if (checkerResult == null) {
	          return null;
	        }
	        if (checkerResult.data && has(checkerResult.data, 'expectedType')) {
	          expectedTypes.push(checkerResult.data.expectedType);
	        }
	      }
	      var expectedTypesMessage = (expectedTypes.length > 0) ? ', expected one of type [' + expectedTypes.join(', ') + ']': '';
	      return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` supplied to ' + ('`' + componentName + '`' + expectedTypesMessage + '.'));
	    }
	    return createChainableTypeChecker(validate);
	  }

	  function createNodeChecker() {
	    function validate(props, propName, componentName, location, propFullName) {
	      if (!isNode(props[propName])) {
	        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` supplied to ' + ('`' + componentName + '`, expected a ReactNode.'));
	      }
	      return null;
	    }
	    return createChainableTypeChecker(validate);
	  }

	  function invalidValidatorError(componentName, location, propFullName, key, type) {
	    return new PropTypeError(
	      (componentName || 'React class') + ': ' + location + ' type `' + propFullName + '.' + key + '` is invalid; ' +
	      'it must be a function, usually from the `prop-types` package, but received `' + type + '`.'
	    );
	  }

	  function createShapeTypeChecker(shapeTypes) {
	    function validate(props, propName, componentName, location, propFullName) {
	      var propValue = props[propName];
	      var propType = getPropType(propValue);
	      if (propType !== 'object') {
	        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type `' + propType + '` ' + ('supplied to `' + componentName + '`, expected `object`.'));
	      }
	      for (var key in shapeTypes) {
	        var checker = shapeTypes[key];
	        if (typeof checker !== 'function') {
	          return invalidValidatorError(componentName, location, propFullName, key, getPreciseType(checker));
	        }
	        var error = checker(propValue, key, componentName, location, propFullName + '.' + key, ReactPropTypesSecret);
	        if (error) {
	          return error;
	        }
	      }
	      return null;
	    }
	    return createChainableTypeChecker(validate);
	  }

	  function createStrictShapeTypeChecker(shapeTypes) {
	    function validate(props, propName, componentName, location, propFullName) {
	      var propValue = props[propName];
	      var propType = getPropType(propValue);
	      if (propType !== 'object') {
	        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type `' + propType + '` ' + ('supplied to `' + componentName + '`, expected `object`.'));
	      }
	      // We need to check all keys in case some are required but missing from props.
	      var allKeys = assign({}, props[propName], shapeTypes);
	      for (var key in allKeys) {
	        var checker = shapeTypes[key];
	        if (has(shapeTypes, key) && typeof checker !== 'function') {
	          return invalidValidatorError(componentName, location, propFullName, key, getPreciseType(checker));
	        }
	        if (!checker) {
	          return new PropTypeError(
	            'Invalid ' + location + ' `' + propFullName + '` key `' + key + '` supplied to `' + componentName + '`.' +
	            '\nBad object: ' + JSON.stringify(props[propName], null, '  ') +
	            '\nValid keys: ' + JSON.stringify(Object.keys(shapeTypes), null, '  ')
	          );
	        }
	        var error = checker(propValue, key, componentName, location, propFullName + '.' + key, ReactPropTypesSecret);
	        if (error) {
	          return error;
	        }
	      }
	      return null;
	    }

	    return createChainableTypeChecker(validate);
	  }

	  function isNode(propValue) {
	    switch (typeof propValue) {
	      case 'number':
	      case 'string':
	      case 'undefined':
	        return true;
	      case 'boolean':
	        return !propValue;
	      case 'object':
	        if (Array.isArray(propValue)) {
	          return propValue.every(isNode);
	        }
	        if (propValue === null || isValidElement(propValue)) {
	          return true;
	        }

	        var iteratorFn = getIteratorFn(propValue);
	        if (iteratorFn) {
	          var iterator = iteratorFn.call(propValue);
	          var step;
	          if (iteratorFn !== propValue.entries) {
	            while (!(step = iterator.next()).done) {
	              if (!isNode(step.value)) {
	                return false;
	              }
	            }
	          } else {
	            // Iterator will provide entry [k,v] tuples rather than values.
	            while (!(step = iterator.next()).done) {
	              var entry = step.value;
	              if (entry) {
	                if (!isNode(entry[1])) {
	                  return false;
	                }
	              }
	            }
	          }
	        } else {
	          return false;
	        }

	        return true;
	      default:
	        return false;
	    }
	  }

	  function isSymbol(propType, propValue) {
	    // Native Symbol.
	    if (propType === 'symbol') {
	      return true;
	    }

	    // falsy value can't be a Symbol
	    if (!propValue) {
	      return false;
	    }

	    // 19.4.3.5 Symbol.prototype[@@toStringTag] === 'Symbol'
	    if (propValue['@@toStringTag'] === 'Symbol') {
	      return true;
	    }

	    // Fallback for non-spec compliant Symbols which are polyfilled.
	    if (typeof Symbol === 'function' && propValue instanceof Symbol) {
	      return true;
	    }

	    return false;
	  }

	  // Equivalent of `typeof` but with special handling for array and regexp.
	  function getPropType(propValue) {
	    var propType = typeof propValue;
	    if (Array.isArray(propValue)) {
	      return 'array';
	    }
	    if (propValue instanceof RegExp) {
	      // Old webkits (at least until Android 4.0) return 'function' rather than
	      // 'object' for typeof a RegExp. We'll normalize this here so that /bla/
	      // passes PropTypes.object.
	      return 'object';
	    }
	    if (isSymbol(propType, propValue)) {
	      return 'symbol';
	    }
	    return propType;
	  }

	  // This handles more types than `getPropType`. Only used for error messages.
	  // See `createPrimitiveTypeChecker`.
	  function getPreciseType(propValue) {
	    if (typeof propValue === 'undefined' || propValue === null) {
	      return '' + propValue;
	    }
	    var propType = getPropType(propValue);
	    if (propType === 'object') {
	      if (propValue instanceof Date) {
	        return 'date';
	      } else if (propValue instanceof RegExp) {
	        return 'regexp';
	      }
	    }
	    return propType;
	  }

	  // Returns a string that is postfixed to a warning about an invalid type.
	  // For example, "undefined" or "of type array"
	  function getPostfixForTypeWarning(value) {
	    var type = getPreciseType(value);
	    switch (type) {
	      case 'array':
	      case 'object':
	        return 'an ' + type;
	      case 'boolean':
	      case 'date':
	      case 'regexp':
	        return 'a ' + type;
	      default:
	        return type;
	    }
	  }

	  // Returns class name of the object, if any.
	  function getClassName(propValue) {
	    if (!propValue.constructor || !propValue.constructor.name) {
	      return ANONYMOUS;
	    }
	    return propValue.constructor.name;
	  }

	  ReactPropTypes.checkPropTypes = checkPropTypes;
	  ReactPropTypes.resetWarningCache = checkPropTypes.resetWarningCache;
	  ReactPropTypes.PropTypes = ReactPropTypes;

	  return ReactPropTypes;
	};
	return factoryWithTypeCheckers;
}

/**
 * Copyright (c) 2013-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

{
  var ReactIs = requireReactIs();

  // By explicitly using `prop-types` you are opting into new development behavior.
  // http://fb.me/prop-types-in-prod
  var throwOnDirectAccess = true;
  propTypes.exports = requireFactoryWithTypeCheckers()(ReactIs.isElement, throwOnDirectAccess);
}

var propTypesExports = propTypes.exports;

var TransitionGroup = {exports: {}};

var chainFunction = function chain(){
  var len = arguments.length;
  var args = [];

  for (var i = 0; i < len; i++)
    args[i] = arguments[i];

  args = args.filter(function(fn){ return fn != null });

  if (args.length === 0) return undefined
  if (args.length === 1) return args[0]

  return args.reduce(function(current, next){
    return function chainedFunction() {
      current.apply(this, arguments);
      next.apply(this, arguments);
    };
  })
};

/**
 * Copyright 2014-2015, Facebook, Inc.
 * All rights reserved.
 *
 * This source code is licensed under the BSD-style license found in the
 * LICENSE file in the root directory of this source tree. An additional grant
 * of patent rights can be found in the PATENTS file in the same directory.
 */

/**
 * Similar to invariant but only logs a warning if the condition is not met.
 * This can be used to log issues in development environments in critical
 * paths. Removing the logging code for production environments will keep the
 * same logic and follow the same code paths.
 */

var warning = function() {};

{
  warning = function(condition, format, args) {
    var len = arguments.length;
    args = new Array(len > 2 ? len - 2 : 0);
    for (var key = 2; key < len; key++) {
      args[key - 2] = arguments[key];
    }
    if (format === undefined) {
      throw new Error(
        '`warning(condition, format, ...args)` requires a warning ' +
        'message argument'
      );
    }

    if (format.length < 10 || (/^[s\W]*$/).test(format)) {
      throw new Error(
        'The warning format should be able to uniquely identify this ' +
        'warning. Please, use a more descriptive format than: ' + format
      );
    }

    if (!condition) {
      var argIndex = 0;
      var message = 'Warning: ' +
        format.replace(/%s/g, function() {
          return args[argIndex++];
        });
      if (typeof console !== 'undefined') {
        console.error(message);
      }
      try {
        // This error was thrown as a convenience so that you can use this stack
        // to find the callsite that caused this warning to fire.
        throw new Error(message);
      } catch(x) {}
    }
  };
}

var browser = warning;

/**
 * Copyright (c) 2013-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

function componentWillMount() {
  // Call this.constructor.gDSFP to support sub-classes.
  var state = this.constructor.getDerivedStateFromProps(this.props, this.state);
  if (state !== null && state !== undefined) {
    this.setState(state);
  }
}

function componentWillReceiveProps(nextProps) {
  // Call this.constructor.gDSFP to support sub-classes.
  // Use the setState() updater to ensure state isn't stale in certain edge cases.
  function updater(prevState) {
    var state = this.constructor.getDerivedStateFromProps(nextProps, prevState);
    return state !== null && state !== undefined ? state : null;
  }
  // Binding "this" is important for shallow renderer support.
  this.setState(updater.bind(this));
}

function componentWillUpdate(nextProps, nextState) {
  try {
    var prevProps = this.props;
    var prevState = this.state;
    this.props = nextProps;
    this.state = nextState;
    this.__reactInternalSnapshotFlag = true;
    this.__reactInternalSnapshot = this.getSnapshotBeforeUpdate(
      prevProps,
      prevState
    );
  } finally {
    this.props = prevProps;
    this.state = prevState;
  }
}

// React may warn about cWM/cWRP/cWU methods being deprecated.
// Add a flag to suppress these warnings for this special case.
componentWillMount.__suppressDeprecationWarning = true;
componentWillReceiveProps.__suppressDeprecationWarning = true;
componentWillUpdate.__suppressDeprecationWarning = true;

function polyfill(Component) {
  var prototype = Component.prototype;

  if (!prototype || !prototype.isReactComponent) {
    throw new Error('Can only polyfill class components');
  }

  if (
    typeof Component.getDerivedStateFromProps !== 'function' &&
    typeof prototype.getSnapshotBeforeUpdate !== 'function'
  ) {
    return Component;
  }

  // If new component APIs are defined, "unsafe" lifecycles won't be called.
  // Error if any of these lifecycles are present,
  // Because they would work differently between older and newer (16.3+) versions of React.
  var foundWillMountName = null;
  var foundWillReceivePropsName = null;
  var foundWillUpdateName = null;
  if (typeof prototype.componentWillMount === 'function') {
    foundWillMountName = 'componentWillMount';
  } else if (typeof prototype.UNSAFE_componentWillMount === 'function') {
    foundWillMountName = 'UNSAFE_componentWillMount';
  }
  if (typeof prototype.componentWillReceiveProps === 'function') {
    foundWillReceivePropsName = 'componentWillReceiveProps';
  } else if (typeof prototype.UNSAFE_componentWillReceiveProps === 'function') {
    foundWillReceivePropsName = 'UNSAFE_componentWillReceiveProps';
  }
  if (typeof prototype.componentWillUpdate === 'function') {
    foundWillUpdateName = 'componentWillUpdate';
  } else if (typeof prototype.UNSAFE_componentWillUpdate === 'function') {
    foundWillUpdateName = 'UNSAFE_componentWillUpdate';
  }
  if (
    foundWillMountName !== null ||
    foundWillReceivePropsName !== null ||
    foundWillUpdateName !== null
  ) {
    var componentName = Component.displayName || Component.name;
    var newApiName =
      typeof Component.getDerivedStateFromProps === 'function'
        ? 'getDerivedStateFromProps()'
        : 'getSnapshotBeforeUpdate()';

    throw Error(
      'Unsafe legacy lifecycles will not be called for components using new component APIs.\n\n' +
        componentName +
        ' uses ' +
        newApiName +
        ' but also contains the following legacy lifecycles:' +
        (foundWillMountName !== null ? '\n  ' + foundWillMountName : '') +
        (foundWillReceivePropsName !== null
          ? '\n  ' + foundWillReceivePropsName
          : '') +
        (foundWillUpdateName !== null ? '\n  ' + foundWillUpdateName : '') +
        '\n\nThe above lifecycles should be removed. Learn more about this warning here:\n' +
        'https://fb.me/react-async-component-lifecycle-hooks'
    );
  }

  // React <= 16.2 does not support static getDerivedStateFromProps.
  // As a workaround, use cWM and cWRP to invoke the new static lifecycle.
  // Newer versions of React will ignore these lifecycles if gDSFP exists.
  if (typeof Component.getDerivedStateFromProps === 'function') {
    prototype.componentWillMount = componentWillMount;
    prototype.componentWillReceiveProps = componentWillReceiveProps;
  }

  // React <= 16.2 does not support getSnapshotBeforeUpdate.
  // As a workaround, use cWU to invoke the new lifecycle.
  // Newer versions of React will ignore that lifecycle if gSBU exists.
  if (typeof prototype.getSnapshotBeforeUpdate === 'function') {
    if (typeof prototype.componentDidUpdate !== 'function') {
      throw new Error(
        'Cannot polyfill getSnapshotBeforeUpdate() for components that do not define componentDidUpdate() on the prototype'
      );
    }

    prototype.componentWillUpdate = componentWillUpdate;

    var componentDidUpdate = prototype.componentDidUpdate;

    prototype.componentDidUpdate = function componentDidUpdatePolyfill(
      prevProps,
      prevState,
      maybeSnapshot
    ) {
      // 16.3+ will not execute our will-update method;
      // It will pass a snapshot value to did-update though.
      // Older versions will require our polyfilled will-update value.
      // We need to handle both cases, but can't just check for the presence of "maybeSnapshot",
      // Because for <= 15.x versions this might be a "prevContext" object.
      // We also can't just check "__reactInternalSnapshot",
      // Because get-snapshot might return a falsy value.
      // So check for the explicit __reactInternalSnapshotFlag flag to determine behavior.
      var snapshot = this.__reactInternalSnapshotFlag
        ? this.__reactInternalSnapshot
        : maybeSnapshot;

      componentDidUpdate.call(this, prevProps, prevState, snapshot);
    };
  }

  return Component;
}

var reactLifecyclesCompat_es = /*#__PURE__*/Object.freeze({
    __proto__: null,
    polyfill: polyfill
});

var require$$4 = /*@__PURE__*/getAugmentedNamespace(reactLifecyclesCompat_es);

var ChildMapping = {};

ChildMapping.__esModule = true;
ChildMapping.getChildMapping = getChildMapping;
ChildMapping.mergeChildMappings = mergeChildMappings;

var _react$1 = React__default;

/**
 * Given `this.props.children`, return an object mapping key to child.
 *
 * @param {*} children `this.props.children`
 * @return {object} Mapping of key to child
 */
function getChildMapping(children) {
  if (!children) {
    return children;
  }
  var result = {};
  _react$1.Children.map(children, function (child) {
    return child;
  }).forEach(function (child) {
    result[child.key] = child;
  });
  return result;
}

/**
 * When you're adding or removing children some may be added or removed in the
 * same render pass. We want to show *both* since we want to simultaneously
 * animate elements in and out. This function takes a previous set of keys
 * and a new set of keys and merges them with its best guess of the correct
 * ordering. In the future we may expose some of the utilities in
 * ReactMultiChild to make this easy, but for now React itself does not
 * directly have this concept of the union of prevChildren and nextChildren
 * so we implement it here.
 *
 * @param {object} prev prev children as returned from
 * `ReactTransitionChildMapping.getChildMapping()`.
 * @param {object} next next children as returned from
 * `ReactTransitionChildMapping.getChildMapping()`.
 * @return {object} a key set that contains all keys in `prev` and all keys
 * in `next` in a reasonable order.
 */
function mergeChildMappings(prev, next) {
  prev = prev || {};
  next = next || {};

  function getValueForKey(key) {
    if (next.hasOwnProperty(key)) {
      return next[key];
    }

    return prev[key];
  }

  // For each key of `next`, the list of keys to insert before that key in
  // the combined list
  var nextKeysPending = {};

  var pendingKeys = [];
  for (var prevKey in prev) {
    if (next.hasOwnProperty(prevKey)) {
      if (pendingKeys.length) {
        nextKeysPending[prevKey] = pendingKeys;
        pendingKeys = [];
      }
    } else {
      pendingKeys.push(prevKey);
    }
  }

  var i = void 0;
  var childMapping = {};
  for (var nextKey in next) {
    if (nextKeysPending.hasOwnProperty(nextKey)) {
      for (i = 0; i < nextKeysPending[nextKey].length; i++) {
        var pendingNextKey = nextKeysPending[nextKey][i];
        childMapping[nextKeysPending[nextKey][i]] = getValueForKey(pendingNextKey);
      }
    }
    childMapping[nextKey] = getValueForKey(nextKey);
  }

  // Finally, add the keys which didn't appear before any key in `next`
  for (i = 0; i < pendingKeys.length; i++) {
    childMapping[pendingKeys[i]] = getValueForKey(pendingKeys[i]);
  }

  return childMapping;
}

TransitionGroup.exports;

(function (module, exports) {

	exports.__esModule = true;

	var _extends = Object.assign || function (target) { for (var i = 1; i < arguments.length; i++) { var source = arguments[i]; for (var key in source) { if (Object.prototype.hasOwnProperty.call(source, key)) { target[key] = source[key]; } } } return target; };

	var _chainFunction = chainFunction;

	var _chainFunction2 = _interopRequireDefault(_chainFunction);

	var _react = React__default;

	var _react2 = _interopRequireDefault(_react);

	var _propTypes = propTypesExports;

	var _propTypes2 = _interopRequireDefault(_propTypes);

	var _warning = browser;

	var _warning2 = _interopRequireDefault(_warning);

	var _reactLifecyclesCompat = require$$4;

	var _ChildMapping = ChildMapping;

	function _interopRequireDefault(obj) { return obj && obj.__esModule ? obj : { default: obj }; }

	function _classCallCheck(instance, Constructor) { if (!(instance instanceof Constructor)) { throw new TypeError("Cannot call a class as a function"); } }

	function _possibleConstructorReturn(self, call) { if (!self) { throw new ReferenceError("this hasn't been initialised - super() hasn't been called"); } return call && (typeof call === "object" || typeof call === "function") ? call : self; }

	function _inherits(subClass, superClass) { if (typeof superClass !== "function" && superClass !== null) { throw new TypeError("Super expression must either be null or a function, not " + typeof superClass); } subClass.prototype = Object.create(superClass && superClass.prototype, { constructor: { value: subClass, enumerable: false, writable: true, configurable: true } }); if (superClass) Object.setPrototypeOf ? Object.setPrototypeOf(subClass, superClass) : subClass.__proto__ = superClass; }

	var propTypes = {
	  component: _propTypes2.default.any,
	  childFactory: _propTypes2.default.func,
	  children: _propTypes2.default.node
	};

	var defaultProps = {
	  component: 'span',
	  childFactory: function childFactory(child) {
	    return child;
	  }
	};

	var TransitionGroup = function (_React$Component) {
	  _inherits(TransitionGroup, _React$Component);

	  function TransitionGroup(props, context) {
	    _classCallCheck(this, TransitionGroup);

	    var _this = _possibleConstructorReturn(this, _React$Component.call(this, props, context));

	    _this.performAppear = function (key, component) {
	      _this.currentlyTransitioningKeys[key] = true;

	      if (component.componentWillAppear) {
	        component.componentWillAppear(_this._handleDoneAppearing.bind(_this, key, component));
	      } else {
	        _this._handleDoneAppearing(key, component);
	      }
	    };

	    _this._handleDoneAppearing = function (key, component) {
	      if (component && component.componentDidAppear) {
	        component.componentDidAppear();
	      }

	      delete _this.currentlyTransitioningKeys[key];

	      var currentChildMapping = (0, _ChildMapping.getChildMapping)(_this.props.children);

	      if (!currentChildMapping || !currentChildMapping.hasOwnProperty(key)) {
	        // This was removed before it had fully appeared. Remove it.
	        _this.performLeave(key, component);
	      }
	    };

	    _this.performEnter = function (key, component) {
	      _this.currentlyTransitioningKeys[key] = true;

	      if (component.componentWillEnter) {
	        component.componentWillEnter(_this._handleDoneEntering.bind(_this, key, component));
	      } else {
	        _this._handleDoneEntering(key, component);
	      }
	    };

	    _this._handleDoneEntering = function (key, component) {
	      if (component && component.componentDidEnter) {
	        component.componentDidEnter();
	      }

	      delete _this.currentlyTransitioningKeys[key];

	      var currentChildMapping = (0, _ChildMapping.getChildMapping)(_this.props.children);

	      if (!currentChildMapping || !currentChildMapping.hasOwnProperty(key)) {
	        // This was removed before it had fully entered. Remove it.
	        _this.performLeave(key, component);
	      }
	    };

	    _this.performLeave = function (key, component) {
	      _this.currentlyTransitioningKeys[key] = true;

	      if (component && component.componentWillLeave) {
	        component.componentWillLeave(_this._handleDoneLeaving.bind(_this, key, component));
	      } else {
	        // Note that this is somewhat dangerous b/c it calls setState()
	        // again, effectively mutating the component before all the work
	        // is done.
	        _this._handleDoneLeaving(key, component);
	      }
	    };

	    _this._handleDoneLeaving = function (key, component) {
	      if (component && component.componentDidLeave) {
	        component.componentDidLeave();
	      }

	      delete _this.currentlyTransitioningKeys[key];

	      var currentChildMapping = (0, _ChildMapping.getChildMapping)(_this.props.children);

	      if (currentChildMapping && currentChildMapping.hasOwnProperty(key)) {
	        // This entered again before it fully left. Add it again.
	        _this.keysToEnter.push(key);
	      } else {
	        _this.setState(function (state) {
	          var newChildren = _extends({}, state.children);
	          delete newChildren[key];
	          return { children: newChildren };
	        });
	      }
	    };

	    _this.childRefs = Object.create(null);
	    _this.currentlyTransitioningKeys = {};
	    _this.keysToEnter = [];
	    _this.keysToLeave = [];

	    _this.state = {
	      children: (0, _ChildMapping.getChildMapping)(props.children)
	    };
	    return _this;
	  }

	  TransitionGroup.prototype.componentDidMount = function componentDidMount() {
	    var initialChildMapping = this.state.children;
	    for (var key in initialChildMapping) {
	      if (initialChildMapping[key]) {
	        this.performAppear(key, this.childRefs[key]);
	      }
	    }
	  };

	  TransitionGroup.getDerivedStateFromProps = function getDerivedStateFromProps(props, state) {
	    var nextChildMapping = (0, _ChildMapping.getChildMapping)(props.children);
	    var prevChildMapping = state.children;

	    return {
	      children: (0, _ChildMapping.mergeChildMappings)(prevChildMapping, nextChildMapping)
	    };
	  };

	  TransitionGroup.prototype.componentDidUpdate = function componentDidUpdate(prevProps, prevState) {
	    var _this2 = this;

	    var nextChildMapping = (0, _ChildMapping.getChildMapping)(this.props.children);
	    var prevChildMapping = prevState.children;

	    for (var key in nextChildMapping) {
	      var hasPrev = prevChildMapping && prevChildMapping.hasOwnProperty(key);
	      if (nextChildMapping[key] && !hasPrev && !this.currentlyTransitioningKeys[key]) {
	        this.keysToEnter.push(key);
	      }
	    }

	    for (var _key in prevChildMapping) {
	      var hasNext = nextChildMapping && nextChildMapping.hasOwnProperty(_key);
	      if (prevChildMapping[_key] && !hasNext && !this.currentlyTransitioningKeys[_key]) {
	        this.keysToLeave.push(_key);
	      }
	    }

	    // If we want to someday check for reordering, we could do it here.

	    var keysToEnter = this.keysToEnter;
	    this.keysToEnter = [];
	    keysToEnter.forEach(function (key) {
	      return _this2.performEnter(key, _this2.childRefs[key]);
	    });

	    var keysToLeave = this.keysToLeave;
	    this.keysToLeave = [];
	    keysToLeave.forEach(function (key) {
	      return _this2.performLeave(key, _this2.childRefs[key]);
	    });
	  };

	  TransitionGroup.prototype.render = function render() {
	    var _this3 = this;

	    // TODO: we could get rid of the need for the wrapper node
	    // by cloning a single child
	    var childrenToRender = [];

	    var _loop = function _loop(key) {
	      var child = _this3.state.children[key];
	      if (child) {
	        var isCallbackRef = typeof child.ref !== 'string';
	        var factoryChild = _this3.props.childFactory(child);
	        var ref = function ref(r) {
	          _this3.childRefs[key] = r;
	        };

	        (0, _warning2.default)(isCallbackRef, 'string refs are not supported on children of TransitionGroup and will be ignored. ' + 'Please use a callback ref instead: https://facebook.github.io/react/docs/refs-and-the-dom.html#the-ref-callback-attribute') ;

	        // Always chaining the refs leads to problems when the childFactory
	        // wraps the child. The child ref callback gets called twice with the
	        // wrapper and the child. So we only need to chain the ref if the
	        // factoryChild is not different from child.
	        if (factoryChild === child && isCallbackRef) {
	          ref = (0, _chainFunction2.default)(child.ref, ref);
	        }

	        // You may need to apply reactive updates to a child as it is leaving.
	        // The normal React way to do it won't work since the child will have
	        // already been removed. In case you need this behavior you can provide
	        // a childFactory function to wrap every child, even the ones that are
	        // leaving.
	        childrenToRender.push(_react2.default.cloneElement(factoryChild, {
	          key: key,
	          ref: ref
	        }));
	      }
	    };

	    for (var key in this.state.children) {
	      _loop(key);
	    }

	    // Do not forward TransitionGroup props to primitive DOM nodes
	    var props = _extends({}, this.props);
	    delete props.transitionLeave;
	    delete props.transitionName;
	    delete props.transitionAppear;
	    delete props.transitionEnter;
	    delete props.childFactory;
	    delete props.transitionLeaveTimeout;
	    delete props.transitionEnterTimeout;
	    delete props.transitionAppearTimeout;
	    delete props.component;

	    return _react2.default.createElement(this.props.component, props, childrenToRender);
	  };

	  return TransitionGroup;
	}(_react2.default.Component);

	TransitionGroup.displayName = 'TransitionGroup';


	TransitionGroup.propTypes = propTypes ;
	TransitionGroup.defaultProps = defaultProps;

	exports.default = (0, _reactLifecyclesCompat.polyfill)(TransitionGroup);
	module.exports = exports['default']; 
} (TransitionGroup, TransitionGroup.exports));

var TransitionGroupExports = TransitionGroup.exports;

var CSSTransitionGroupChild = {exports: {}};

var addClass = {exports: {}};

var interopRequireDefault = {exports: {}};

interopRequireDefault.exports;

(function (module) {
	function _interopRequireDefault(obj) {
	  return obj && obj.__esModule ? obj : {
	    "default": obj
	  };
	}
	module.exports = _interopRequireDefault, module.exports.__esModule = true, module.exports["default"] = module.exports; 
} (interopRequireDefault));

var interopRequireDefaultExports = interopRequireDefault.exports;

var hasClass = {exports: {}};

hasClass.exports;

var hasRequiredHasClass;

function requireHasClass () {
	if (hasRequiredHasClass) return hasClass.exports;
	hasRequiredHasClass = 1;
	(function (module, exports) {

		exports.__esModule = true;
		exports.default = hasClass;

		function hasClass(element, className) {
		  if (element.classList) return !!className && element.classList.contains(className);else return (" " + (element.className.baseVal || element.className) + " ").indexOf(" " + className + " ") !== -1;
		}

		module.exports = exports["default"]; 
	} (hasClass, hasClass.exports));
	return hasClass.exports;
}

addClass.exports;

(function (module, exports) {

	var _interopRequireDefault = interopRequireDefaultExports;

	exports.__esModule = true;
	exports.default = addClass;

	var _hasClass = _interopRequireDefault(requireHasClass());

	function addClass(element, className) {
	  if (element.classList) element.classList.add(className);else if (!(0, _hasClass.default)(element, className)) if (typeof element.className === 'string') element.className = element.className + ' ' + className;else element.setAttribute('class', (element.className && element.className.baseVal || '') + ' ' + className);
	}

	module.exports = exports["default"]; 
} (addClass, addClass.exports));

var addClassExports = addClass.exports;

function replaceClassName(origClass, classToRemove) {
  return origClass.replace(new RegExp('(^|\\s)' + classToRemove + '(?:\\s|$)', 'g'), '$1').replace(/\s+/g, ' ').replace(/^\s*|\s*$/g, '');
}

var removeClass = function removeClass(element, className) {
  if (element.classList) element.classList.remove(className);else if (typeof element.className === 'string') element.className = replaceClassName(element.className, className);else element.setAttribute('class', replaceClassName(element.className && element.className.baseVal || '', className));
};

var requestAnimationFrame = {exports: {}};

var inDOM = {exports: {}};

inDOM.exports;

var hasRequiredInDOM;

function requireInDOM () {
	if (hasRequiredInDOM) return inDOM.exports;
	hasRequiredInDOM = 1;
	(function (module, exports) {

		exports.__esModule = true;
		exports.default = void 0;

		var _default = !!(window.document && window.document.createElement);

		exports.default = _default;
		module.exports = exports["default"]; 
	} (inDOM, inDOM.exports));
	return inDOM.exports;
}

requestAnimationFrame.exports;

(function (module, exports) {

	var _interopRequireDefault = interopRequireDefaultExports;

	exports.__esModule = true;
	exports.default = void 0;

	var _inDOM = _interopRequireDefault(requireInDOM());

	var vendors = ['', 'webkit', 'moz', 'o', 'ms'];
	var cancel = 'clearTimeout';
	var raf = fallback;
	var compatRaf;

	var getKey = function getKey(vendor, k) {
	  return vendor + (!vendor ? k : k[0].toUpperCase() + k.substr(1)) + 'AnimationFrame';
	};

	if (_inDOM.default) {
	  vendors.some(function (vendor) {
	    var rafKey = getKey(vendor, 'request');

	    if (rafKey in window) {
	      cancel = getKey(vendor, 'cancel');
	      return raf = function raf(cb) {
	        return window[rafKey](cb);
	      };
	    }
	  });
	}
	/* https://github.com/component/raf */


	var prev = new Date().getTime();

	function fallback(fn) {
	  var curr = new Date().getTime(),
	      ms = Math.max(0, 16 - (curr - prev)),
	      req = setTimeout(fn, ms);
	  prev = curr;
	  return req;
	}

	compatRaf = function compatRaf(cb) {
	  return raf(cb);
	};

	compatRaf.cancel = function (id) {
	  window[cancel] && "object"[cancel] === 'function' && window[cancel](id);
	};

	var _default = compatRaf;
	exports.default = _default;
	module.exports = exports["default"]; 
} (requestAnimationFrame, requestAnimationFrame.exports));

var requestAnimationFrameExports = requestAnimationFrame.exports;

var properties = {};

var _interopRequireDefault$2 = interopRequireDefaultExports;

properties.__esModule = true;
properties.default = properties.animationEnd = properties.animationDelay = properties.animationTiming = properties.animationDuration = properties.animationName = properties.transitionEnd = properties.transitionDuration = properties.transitionDelay = properties.transitionTiming = properties.transitionProperty = properties.transform = void 0;

var _inDOM = _interopRequireDefault$2(requireInDOM());

var transform = 'transform';
properties.transform = transform;
var prefix, transitionEnd, animationEnd;
properties.animationEnd = animationEnd;
properties.transitionEnd = transitionEnd;
var transitionProperty, transitionDuration, transitionTiming, transitionDelay;
properties.transitionDelay = transitionDelay;
properties.transitionTiming = transitionTiming;
properties.transitionDuration = transitionDuration;
properties.transitionProperty = transitionProperty;
var animationName, animationDuration, animationTiming, animationDelay;
properties.animationDelay = animationDelay;
properties.animationTiming = animationTiming;
properties.animationDuration = animationDuration;
properties.animationName = animationName;

if (_inDOM.default) {
  var _getTransitionPropert = getTransitionProperties();

  prefix = _getTransitionPropert.prefix;
  properties.transitionEnd = transitionEnd = _getTransitionPropert.transitionEnd;
  properties.animationEnd = animationEnd = _getTransitionPropert.animationEnd;
  properties.transform = transform = prefix + "-" + transform;
  properties.transitionProperty = transitionProperty = prefix + "-transition-property";
  properties.transitionDuration = transitionDuration = prefix + "-transition-duration";
  properties.transitionDelay = transitionDelay = prefix + "-transition-delay";
  properties.transitionTiming = transitionTiming = prefix + "-transition-timing-function";
  properties.animationName = animationName = prefix + "-animation-name";
  properties.animationDuration = animationDuration = prefix + "-animation-duration";
  properties.animationTiming = animationTiming = prefix + "-animation-delay";
  properties.animationDelay = animationDelay = prefix + "-animation-timing-function";
}

var _default = {
  transform: transform,
  end: transitionEnd,
  property: transitionProperty,
  timing: transitionTiming,
  delay: transitionDelay,
  duration: transitionDuration
};
properties.default = _default;

function getTransitionProperties() {
  var style = document.createElement('div').style;
  var vendorMap = {
    O: function O(e) {
      return "o" + e.toLowerCase();
    },
    Moz: function Moz(e) {
      return e.toLowerCase();
    },
    Webkit: function Webkit(e) {
      return "webkit" + e;
    },
    ms: function ms(e) {
      return "MS" + e;
    }
  };
  var vendors = Object.keys(vendorMap);
  var transitionEnd, animationEnd;
  var prefix = '';

  for (var i = 0; i < vendors.length; i++) {
    var vendor = vendors[i];

    if (vendor + "TransitionProperty" in style) {
      prefix = "-" + vendor.toLowerCase();
      transitionEnd = vendorMap[vendor]('TransitionEnd');
      animationEnd = vendorMap[vendor]('AnimationEnd');
      break;
    }
  }

  if (!transitionEnd && 'transitionProperty' in style) transitionEnd = 'transitionend';
  if (!animationEnd && 'animationName' in style) animationEnd = 'animationend';
  style = null;
  return {
    animationEnd: animationEnd,
    transitionEnd: transitionEnd,
    prefix: prefix
  };
}

var PropTypes = {};

PropTypes.__esModule = true;
PropTypes.nameShape = undefined;
PropTypes.transitionTimeout = transitionTimeout;

var _react = React__default;

_interopRequireDefault$1(_react);

var _propTypes = propTypesExports;

var _propTypes2 = _interopRequireDefault$1(_propTypes);

function _interopRequireDefault$1(obj) { return obj && obj.__esModule ? obj : { default: obj }; }

function transitionTimeout(transitionType) {
  var timeoutPropName = 'transition' + transitionType + 'Timeout';
  var enabledPropName = 'transition' + transitionType;

  return function (props) {
    // If the transition is enabled
    if (props[enabledPropName]) {
      // If no timeout duration is provided
      if (props[timeoutPropName] == null) {
        return new Error(timeoutPropName + ' wasn\'t supplied to CSSTransitionGroup: ' + 'this can cause unreliable animations and won\'t be supported in ' + 'a future version of React. See ' + 'https://fb.me/react-animation-transition-group-timeout for more ' + 'information.');

        // If the duration isn't a number
      } else if (typeof props[timeoutPropName] !== 'number') {
        return new Error(timeoutPropName + ' must be a number (in milliseconds)');
      }
    }

    return null;
  };
}

PropTypes.nameShape = _propTypes2.default.oneOfType([_propTypes2.default.string, _propTypes2.default.shape({
  enter: _propTypes2.default.string,
  leave: _propTypes2.default.string,
  active: _propTypes2.default.string
}), _propTypes2.default.shape({
  enter: _propTypes2.default.string,
  enterActive: _propTypes2.default.string,
  leave: _propTypes2.default.string,
  leaveActive: _propTypes2.default.string,
  appear: _propTypes2.default.string,
  appearActive: _propTypes2.default.string
})]);

CSSTransitionGroupChild.exports;

(function (module, exports) {

	exports.__esModule = true;

	var _extends = Object.assign || function (target) { for (var i = 1; i < arguments.length; i++) { var source = arguments[i]; for (var key in source) { if (Object.prototype.hasOwnProperty.call(source, key)) { target[key] = source[key]; } } } return target; };

	var _addClass = addClassExports;

	var _addClass2 = _interopRequireDefault(_addClass);

	var _removeClass = removeClass;

	var _removeClass2 = _interopRequireDefault(_removeClass);

	var _requestAnimationFrame = requestAnimationFrameExports;

	var _requestAnimationFrame2 = _interopRequireDefault(_requestAnimationFrame);

	var _properties = properties;

	var _react = React__default;

	var _react2 = _interopRequireDefault(_react);

	var _propTypes = propTypesExports;

	var _propTypes2 = _interopRequireDefault(_propTypes);

	var _reactDom = require$$6;

	var _PropTypes = PropTypes;

	function _interopRequireDefault(obj) { return obj && obj.__esModule ? obj : { default: obj }; }

	function _classCallCheck(instance, Constructor) { if (!(instance instanceof Constructor)) { throw new TypeError("Cannot call a class as a function"); } }

	function _possibleConstructorReturn(self, call) { if (!self) { throw new ReferenceError("this hasn't been initialised - super() hasn't been called"); } return call && (typeof call === "object" || typeof call === "function") ? call : self; }

	function _inherits(subClass, superClass) { if (typeof superClass !== "function" && superClass !== null) { throw new TypeError("Super expression must either be null or a function, not " + typeof superClass); } subClass.prototype = Object.create(superClass && superClass.prototype, { constructor: { value: subClass, enumerable: false, writable: true, configurable: true } }); if (superClass) Object.setPrototypeOf ? Object.setPrototypeOf(subClass, superClass) : subClass.__proto__ = superClass; }

	var events = [];
	if (_properties.transitionEnd) events.push(_properties.transitionEnd);
	if (_properties.animationEnd) events.push(_properties.animationEnd);

	function addEndListener(node, listener) {
	  if (events.length) {
	    events.forEach(function (e) {
	      return node.addEventListener(e, listener, false);
	    });
	  } else {
	    setTimeout(listener, 0);
	  }

	  return function () {
	    if (!events.length) return;
	    events.forEach(function (e) {
	      return node.removeEventListener(e, listener, false);
	    });
	  };
	}

	var propTypes = {
	  children: _propTypes2.default.node,
	  name: _PropTypes.nameShape.isRequired,

	  // Once we require timeouts to be specified, we can remove the
	  // boolean flags (appear etc.) and just accept a number
	  // or a bool for the timeout flags (appearTimeout etc.)
	  appear: _propTypes2.default.bool,
	  enter: _propTypes2.default.bool,
	  leave: _propTypes2.default.bool,
	  appearTimeout: _propTypes2.default.number,
	  enterTimeout: _propTypes2.default.number,
	  leaveTimeout: _propTypes2.default.number
	};

	var CSSTransitionGroupChild = function (_React$Component) {
	  _inherits(CSSTransitionGroupChild, _React$Component);

	  function CSSTransitionGroupChild(props, context) {
	    _classCallCheck(this, CSSTransitionGroupChild);

	    var _this = _possibleConstructorReturn(this, _React$Component.call(this, props, context));

	    _this.componentWillAppear = function (done) {
	      if (_this.props.appear) {
	        _this.transition('appear', done, _this.props.appearTimeout);
	      } else {
	        done();
	      }
	    };

	    _this.componentWillEnter = function (done) {
	      if (_this.props.enter) {
	        _this.transition('enter', done, _this.props.enterTimeout);
	      } else {
	        done();
	      }
	    };

	    _this.componentWillLeave = function (done) {
	      if (_this.props.leave) {
	        _this.transition('leave', done, _this.props.leaveTimeout);
	      } else {
	        done();
	      }
	    };

	    _this.classNameAndNodeQueue = [];
	    _this.transitionTimeouts = [];
	    return _this;
	  }

	  CSSTransitionGroupChild.prototype.componentWillUnmount = function componentWillUnmount() {
	    this.unmounted = true;

	    if (this.timeout) {
	      clearTimeout(this.timeout);
	    }
	    this.transitionTimeouts.forEach(function (timeout) {
	      clearTimeout(timeout);
	    });

	    this.classNameAndNodeQueue.length = 0;
	  };

	  CSSTransitionGroupChild.prototype.transition = function transition(animationType, finishCallback, timeout) {
	    var node = (0, _reactDom.findDOMNode)(this);

	    if (!node) {
	      if (finishCallback) {
	        finishCallback();
	      }
	      return;
	    }

	    var className = this.props.name[animationType] || this.props.name + '-' + animationType;
	    var activeClassName = this.props.name[animationType + 'Active'] || className + '-active';
	    var timer = null;
	    var removeListeners = void 0;

	    (0, _addClass2.default)(node, className);

	    // Need to do this to actually trigger a transition.
	    this.queueClassAndNode(activeClassName, node);

	    // Clean-up the animation after the specified delay
	    var finish = function finish(e) {
	      if (e && e.target !== node) {
	        return;
	      }

	      clearTimeout(timer);
	      if (removeListeners) removeListeners();

	      (0, _removeClass2.default)(node, className);
	      (0, _removeClass2.default)(node, activeClassName);

	      if (removeListeners) removeListeners();

	      // Usually this optional callback is used for informing an owner of
	      // a leave animation and telling it to remove the child.
	      if (finishCallback) {
	        finishCallback();
	      }
	    };

	    if (timeout) {
	      timer = setTimeout(finish, timeout);
	      this.transitionTimeouts.push(timer);
	    } else if (_properties.transitionEnd) {
	      removeListeners = addEndListener(node, finish);
	    }
	  };

	  CSSTransitionGroupChild.prototype.queueClassAndNode = function queueClassAndNode(className, node) {
	    var _this2 = this;

	    this.classNameAndNodeQueue.push({
	      className: className,
	      node: node
	    });

	    if (!this.rafHandle) {
	      this.rafHandle = (0, _requestAnimationFrame2.default)(function () {
	        return _this2.flushClassNameAndNodeQueue();
	      });
	    }
	  };

	  CSSTransitionGroupChild.prototype.flushClassNameAndNodeQueue = function flushClassNameAndNodeQueue() {
	    if (!this.unmounted) {
	      this.classNameAndNodeQueue.forEach(function (obj) {
	        // This is for to force a repaint,
	        // which is necessary in order to transition styles when adding a class name.
	        /* eslint-disable no-unused-expressions */
	        obj.node.scrollTop;
	        /* eslint-enable no-unused-expressions */
	        (0, _addClass2.default)(obj.node, obj.className);
	      });
	    }
	    this.classNameAndNodeQueue.length = 0;
	    this.rafHandle = null;
	  };

	  CSSTransitionGroupChild.prototype.render = function render() {
	    var props = _extends({}, this.props);
	    delete props.name;
	    delete props.appear;
	    delete props.enter;
	    delete props.leave;
	    delete props.appearTimeout;
	    delete props.enterTimeout;
	    delete props.leaveTimeout;
	    delete props.children;
	    return _react2.default.cloneElement(_react2.default.Children.only(this.props.children), props);
	  };

	  return CSSTransitionGroupChild;
	}(_react2.default.Component);

	CSSTransitionGroupChild.displayName = 'CSSTransitionGroupChild';


	CSSTransitionGroupChild.propTypes = propTypes ;

	exports.default = CSSTransitionGroupChild;
	module.exports = exports['default']; 
} (CSSTransitionGroupChild, CSSTransitionGroupChild.exports));

var CSSTransitionGroupChildExports = CSSTransitionGroupChild.exports;

CSSTransitionGroup.exports;

(function (module, exports) {

	exports.__esModule = true;

	var _extends = Object.assign || function (target) { for (var i = 1; i < arguments.length; i++) { var source = arguments[i]; for (var key in source) { if (Object.prototype.hasOwnProperty.call(source, key)) { target[key] = source[key]; } } } return target; };

	var _react = React__default;

	var _react2 = _interopRequireDefault(_react);

	var _propTypes = propTypesExports;

	var _propTypes2 = _interopRequireDefault(_propTypes);

	var _TransitionGroup = TransitionGroupExports;

	var _TransitionGroup2 = _interopRequireDefault(_TransitionGroup);

	var _CSSTransitionGroupChild = CSSTransitionGroupChildExports;

	var _CSSTransitionGroupChild2 = _interopRequireDefault(_CSSTransitionGroupChild);

	var _PropTypes = PropTypes;

	function _interopRequireDefault(obj) { return obj && obj.__esModule ? obj : { default: obj }; }

	function _classCallCheck(instance, Constructor) { if (!(instance instanceof Constructor)) { throw new TypeError("Cannot call a class as a function"); } }

	function _possibleConstructorReturn(self, call) { if (!self) { throw new ReferenceError("this hasn't been initialised - super() hasn't been called"); } return call && (typeof call === "object" || typeof call === "function") ? call : self; }

	function _inherits(subClass, superClass) { if (typeof superClass !== "function" && superClass !== null) { throw new TypeError("Super expression must either be null or a function, not " + typeof superClass); } subClass.prototype = Object.create(superClass && superClass.prototype, { constructor: { value: subClass, enumerable: false, writable: true, configurable: true } }); if (superClass) Object.setPrototypeOf ? Object.setPrototypeOf(subClass, superClass) : subClass.__proto__ = superClass; }

	var propTypes = {
	  transitionName: _PropTypes.nameShape.isRequired,

	  transitionAppear: _propTypes2.default.bool,
	  transitionEnter: _propTypes2.default.bool,
	  transitionLeave: _propTypes2.default.bool,
	  transitionAppearTimeout: (0, _PropTypes.transitionTimeout)('Appear'),
	  transitionEnterTimeout: (0, _PropTypes.transitionTimeout)('Enter'),
	  transitionLeaveTimeout: (0, _PropTypes.transitionTimeout)('Leave')
	};

	var defaultProps = {
	  transitionAppear: false,
	  transitionEnter: true,
	  transitionLeave: true
	};

	var CSSTransitionGroup = function (_React$Component) {
	  _inherits(CSSTransitionGroup, _React$Component);

	  function CSSTransitionGroup() {
	    var _temp, _this, _ret;

	    _classCallCheck(this, CSSTransitionGroup);

	    for (var _len = arguments.length, args = Array(_len), _key = 0; _key < _len; _key++) {
	      args[_key] = arguments[_key];
	    }

	    return _ret = (_temp = (_this = _possibleConstructorReturn(this, _React$Component.call.apply(_React$Component, [this].concat(args))), _this), _this._wrapChild = function (child) {
	      return _react2.default.createElement(_CSSTransitionGroupChild2.default, {
	        name: _this.props.transitionName,
	        appear: _this.props.transitionAppear,
	        enter: _this.props.transitionEnter,
	        leave: _this.props.transitionLeave,
	        appearTimeout: _this.props.transitionAppearTimeout,
	        enterTimeout: _this.props.transitionEnterTimeout,
	        leaveTimeout: _this.props.transitionLeaveTimeout
	      }, child);
	    }, _temp), _possibleConstructorReturn(_this, _ret);
	  }

	  // We need to provide this childFactory so that
	  // ReactCSSTransitionGroupChild can receive updates to name, enter, and
	  // leave while it is leaving.


	  CSSTransitionGroup.prototype.render = function render() {
	    return _react2.default.createElement(_TransitionGroup2.default, _extends({}, this.props, { childFactory: this._wrapChild }));
	  };

	  return CSSTransitionGroup;
	}(_react2.default.Component);

	CSSTransitionGroup.displayName = 'CSSTransitionGroup';


	CSSTransitionGroup.propTypes = propTypes ;
	CSSTransitionGroup.defaultProps = defaultProps;

	exports.default = CSSTransitionGroup;
	module.exports = exports['default']; 
} (CSSTransitionGroup, CSSTransitionGroup.exports));

var CSSTransitionGroupExports = CSSTransitionGroup.exports;

var _CSSTransitionGroup = CSSTransitionGroupExports;

var _CSSTransitionGroup2 = _interopRequireDefault(_CSSTransitionGroup);

var _TransitionGroup = TransitionGroupExports;

var _TransitionGroup2 = _interopRequireDefault(_TransitionGroup);

function _interopRequireDefault(obj) { return obj && obj.__esModule ? obj : { default: obj }; }

var reactTransitionGroup = {
  TransitionGroup: _TransitionGroup2.default,
  CSSTransitionGroup: _CSSTransitionGroup2.default
};

const TransitionGroupWrapper = (props) => props.enableLegacyTransitions ? (React__default.createElement(reactTransitionGroup.TransitionGroup, { component: props.component, className: props.className, transform: props.transform }, props.children)) : (React__default.createElement("g", { className: props.className, transform: props.transform }, props.children));

const DEFAULT_NODE_CIRCLE_RADIUS = 15;
const textLayout = {
    title: {
        textAnchor: 'start',
        x: 40,
    },
    attribute: {
        x: 40,
        dy: '1.2em',
    },
};
const DefaultNodeElement = ({ nodeDatum, toggleNode, onNodeClick, onNodeMouseOver, onNodeMouseOut, }) => (React__default.createElement(React__default.Fragment, null,
    React__default.createElement("circle", { r: DEFAULT_NODE_CIRCLE_RADIUS, onClick: evt => {
            toggleNode();
            onNodeClick(evt);
        }, onMouseOver: onNodeMouseOver, onMouseOut: onNodeMouseOut }),
    React__default.createElement("g", { className: "rd3t-label" },
        React__default.createElement("text", Object.assign({ className: "rd3t-label__title" }, textLayout.title), nodeDatum.name),
        React__default.createElement("text", { className: "rd3t-label__attributes" }, nodeDatum.attributes &&
            Object.entries(nodeDatum.attributes).map(([labelKey, labelValue], i) => (React__default.createElement("tspan", Object.assign({ key: `${labelKey}-${i}` }, textLayout.attribute),
                labelKey,
                ": ",
                typeof labelValue === 'boolean' ? labelValue.toString() : labelValue)))))));

class Node extends React__default.Component {
    constructor() {
        super(...arguments);
        this.nodeRef = null;
        this.state = {
            transform: this.setTransform(this.props.position, this.props.parent, this.props.orientation, true),
            initialStyle: {
                opacity: 0,
            },
            wasClicked: false,
        };
        this.shouldNodeTransform = (ownProps, nextProps, ownState, nextState) => nextProps.subscriptions !== ownProps.subscriptions ||
            nextProps.position.x !== ownProps.position.x ||
            nextProps.position.y !== ownProps.position.y ||
            nextProps.orientation !== ownProps.orientation ||
            nextState.wasClicked !== ownState.wasClicked;
        // TODO: needs tests
        this.renderNodeElement = () => {
            const { data, hierarchyPointNode, renderCustomNodeElement } = this.props;
            const renderNode = typeof renderCustomNodeElement === 'function' ? renderCustomNodeElement : DefaultNodeElement;
            const nodeProps = {
                hierarchyPointNode: hierarchyPointNode,
                nodeDatum: data,
                toggleNode: this.handleNodeToggle,
                onNodeClick: this.handleOnClick,
                onNodeMouseOver: this.handleOnMouseOver,
                onNodeMouseOut: this.handleOnMouseOut,
                addChildren: this.handleAddChildren,
            };
            return renderNode(nodeProps);
        };
        this.handleNodeToggle = () => {
            this.setState({ wasClicked: true });
            this.props.onNodeToggle(this.props.data.__rd3t.id);
        };
        this.handleOnClick = evt => {
            this.setState({ wasClicked: true });
            this.props.onNodeClick(this.props.hierarchyPointNode, evt);
        };
        this.handleOnMouseOver = evt => {
            this.props.onNodeMouseOver(this.props.hierarchyPointNode, evt);
        };
        this.handleOnMouseOut = evt => {
            this.props.onNodeMouseOut(this.props.hierarchyPointNode, evt);
        };
        this.handleAddChildren = childrenData => {
            this.props.handleAddChildrenToNode(this.props.data.__rd3t.id, childrenData);
        };
    }
    componentDidMount() {
        this.commitTransform();
    }
    componentDidUpdate() {
        if (this.state.wasClicked) {
            this.props.centerNode(this.props.hierarchyPointNode);
            this.setState({ wasClicked: false });
        }
        this.commitTransform();
    }
    shouldComponentUpdate(nextProps, nextState) {
        return this.shouldNodeTransform(this.props, nextProps, this.state, nextState);
    }
    setTransform(position, parent, orientation, shouldTranslateToOrigin = false) {
        if (shouldTranslateToOrigin) {
            const hasParent = parent !== null && parent !== undefined;
            const originX = hasParent ? parent.x : 0;
            const originY = hasParent ? parent.y : 0;
            return orientation === 'horizontal'
                ? `translate(${originY},${originX})`
                : `translate(${originX},${originY})`;
        }
        return orientation === 'horizontal'
            ? `translate(${position.y},${position.x})`
            : `translate(${position.x},${position.y})`;
    }
    applyTransform(transform, transitionDuration, opacity = 1, done = () => { }) {
        if (this.props.enableLegacyTransitions) {
            select(this.nodeRef)
                // @ts-ignore
                .transition()
                .duration(transitionDuration)
                .attr('transform', transform)
                .style('opacity', opacity)
                .on('end', done);
        }
        else {
            select(this.nodeRef)
                .attr('transform', transform)
                .style('opacity', opacity);
            done();
        }
    }
    commitTransform() {
        const { orientation, transitionDuration, position, parent } = this.props;
        const transform = this.setTransform(position, parent, orientation);
        this.applyTransform(transform, transitionDuration);
    }
    componentWillLeave(done) {
        const { orientation, transitionDuration, position, parent } = this.props;
        const transform = this.setTransform(position, parent, orientation, true);
        this.applyTransform(transform, transitionDuration, 0, done);
    }
    render() {
        const { data, nodeClassName } = this.props;
        return (React__default.createElement("g", { id: data.__rd3t.id, ref: n => {
                this.nodeRef = n;
            }, style: this.state.initialStyle, className: [
                data.children && data.children.length > 0 ? 'rd3t-node' : 'rd3t-leaf-node',
                nodeClassName,
            ]
                .join(' ')
                .trim(), transform: this.state.transform }, this.renderNodeElement()));
    }
}

var pi = Math.PI,
    tau = 2 * pi,
    epsilon = 1e-6,
    tauEpsilon = tau - epsilon;

function Path() {
  this._x0 = this._y0 = // start of current subpath
  this._x1 = this._y1 = null; // end of current subpath
  this._ = "";
}

function path() {
  return new Path;
}

Path.prototype = path.prototype = {
  constructor: Path,
  moveTo: function(x, y) {
    this._ += "M" + (this._x0 = this._x1 = +x) + "," + (this._y0 = this._y1 = +y);
  },
  closePath: function() {
    if (this._x1 !== null) {
      this._x1 = this._x0, this._y1 = this._y0;
      this._ += "Z";
    }
  },
  lineTo: function(x, y) {
    this._ += "L" + (this._x1 = +x) + "," + (this._y1 = +y);
  },
  quadraticCurveTo: function(x1, y1, x, y) {
    this._ += "Q" + (+x1) + "," + (+y1) + "," + (this._x1 = +x) + "," + (this._y1 = +y);
  },
  bezierCurveTo: function(x1, y1, x2, y2, x, y) {
    this._ += "C" + (+x1) + "," + (+y1) + "," + (+x2) + "," + (+y2) + "," + (this._x1 = +x) + "," + (this._y1 = +y);
  },
  arcTo: function(x1, y1, x2, y2, r) {
    x1 = +x1, y1 = +y1, x2 = +x2, y2 = +y2, r = +r;
    var x0 = this._x1,
        y0 = this._y1,
        x21 = x2 - x1,
        y21 = y2 - y1,
        x01 = x0 - x1,
        y01 = y0 - y1,
        l01_2 = x01 * x01 + y01 * y01;

    // Is the radius negative? Error.
    if (r < 0) throw new Error("negative radius: " + r);

    // Is this path empty? Move to (x1,y1).
    if (this._x1 === null) {
      this._ += "M" + (this._x1 = x1) + "," + (this._y1 = y1);
    }

    // Or, is (x1,y1) coincident with (x0,y0)? Do nothing.
    else if (!(l01_2 > epsilon));

    // Or, are (x0,y0), (x1,y1) and (x2,y2) collinear?
    // Equivalently, is (x1,y1) coincident with (x2,y2)?
    // Or, is the radius zero? Line to (x1,y1).
    else if (!(Math.abs(y01 * x21 - y21 * x01) > epsilon) || !r) {
      this._ += "L" + (this._x1 = x1) + "," + (this._y1 = y1);
    }

    // Otherwise, draw an arc!
    else {
      var x20 = x2 - x0,
          y20 = y2 - y0,
          l21_2 = x21 * x21 + y21 * y21,
          l20_2 = x20 * x20 + y20 * y20,
          l21 = Math.sqrt(l21_2),
          l01 = Math.sqrt(l01_2),
          l = r * Math.tan((pi - Math.acos((l21_2 + l01_2 - l20_2) / (2 * l21 * l01))) / 2),
          t01 = l / l01,
          t21 = l / l21;

      // If the start tangent is not coincident with (x0,y0), line to.
      if (Math.abs(t01 - 1) > epsilon) {
        this._ += "L" + (x1 + t01 * x01) + "," + (y1 + t01 * y01);
      }

      this._ += "A" + r + "," + r + ",0,0," + (+(y01 * x20 > x01 * y20)) + "," + (this._x1 = x1 + t21 * x21) + "," + (this._y1 = y1 + t21 * y21);
    }
  },
  arc: function(x, y, r, a0, a1, ccw) {
    x = +x, y = +y, r = +r, ccw = !!ccw;
    var dx = r * Math.cos(a0),
        dy = r * Math.sin(a0),
        x0 = x + dx,
        y0 = y + dy,
        cw = 1 ^ ccw,
        da = ccw ? a0 - a1 : a1 - a0;

    // Is the radius negative? Error.
    if (r < 0) throw new Error("negative radius: " + r);

    // Is this path empty? Move to (x0,y0).
    if (this._x1 === null) {
      this._ += "M" + x0 + "," + y0;
    }

    // Or, is (x0,y0) not coincident with the previous point? Line to (x0,y0).
    else if (Math.abs(this._x1 - x0) > epsilon || Math.abs(this._y1 - y0) > epsilon) {
      this._ += "L" + x0 + "," + y0;
    }

    // Is this arc empty? We’re done.
    if (!r) return;

    // Does the angle go the wrong way? Flip the direction.
    if (da < 0) da = da % tau + tau;

    // Is this a complete circle? Draw two arcs to complete the circle.
    if (da > tauEpsilon) {
      this._ += "A" + r + "," + r + ",0,1," + cw + "," + (x - dx) + "," + (y - dy) + "A" + r + "," + r + ",0,1," + cw + "," + (this._x1 = x0) + "," + (this._y1 = y0);
    }

    // Is this arc non-empty? Draw an arc!
    else if (da > epsilon) {
      this._ += "A" + r + "," + r + ",0," + (+(da >= pi)) + "," + cw + "," + (this._x1 = x + r * Math.cos(a1)) + "," + (this._y1 = y + r * Math.sin(a1));
    }
  },
  rect: function(x, y, w, h) {
    this._ += "M" + (this._x0 = this._x1 = +x) + "," + (this._y0 = this._y1 = +y) + "h" + (+w) + "v" + (+h) + "h" + (-w) + "Z";
  },
  toString: function() {
    return this._;
  }
};

function constant(x) {
  return function constant() {
    return x;
  };
}

function x(p) {
  return p[0];
}

function y(p) {
  return p[1];
}

var slice = Array.prototype.slice;

function linkSource(d) {
  return d.source;
}

function linkTarget(d) {
  return d.target;
}

function link(curve) {
  var source = linkSource,
      target = linkTarget,
      x$1 = x,
      y$1 = y,
      context = null;

  function link() {
    var buffer, argv = slice.call(arguments), s = source.apply(this, argv), t = target.apply(this, argv);
    if (!context) context = buffer = path();
    curve(context, +x$1.apply(this, (argv[0] = s, argv)), +y$1.apply(this, argv), +x$1.apply(this, (argv[0] = t, argv)), +y$1.apply(this, argv));
    if (buffer) return context = null, buffer + "" || null;
  }

  link.source = function(_) {
    return arguments.length ? (source = _, link) : source;
  };

  link.target = function(_) {
    return arguments.length ? (target = _, link) : target;
  };

  link.x = function(_) {
    return arguments.length ? (x$1 = typeof _ === "function" ? _ : constant(+_), link) : x$1;
  };

  link.y = function(_) {
    return arguments.length ? (y$1 = typeof _ === "function" ? _ : constant(+_), link) : y$1;
  };

  link.context = function(_) {
    return arguments.length ? ((context = _ == null ? null : _), link) : context;
  };

  return link;
}

function curveHorizontal(context, x0, y0, x1, y1) {
  context.moveTo(x0, y0);
  context.bezierCurveTo(x0 = (x0 + x1) / 2, y0, x0, y1, x1, y1);
}

function curveVertical(context, x0, y0, x1, y1) {
  context.moveTo(x0, y0);
  context.bezierCurveTo(x0, y0 = (y0 + y1) / 2, x1, y0, x1, y1);
}

function linkHorizontal() {
  return link(curveHorizontal);
}

function linkVertical() {
  return link(curveVertical);
}

class Link extends React__default.PureComponent {
    constructor() {
        super(...arguments);
        this.linkRef = null;
        this.state = {
            initialStyle: {
                opacity: 0,
            },
        };
        this.handleOnClick = evt => {
            this.props.onClick(this.props.linkData.source, this.props.linkData.target, evt);
        };
        this.handleOnMouseOver = evt => {
            this.props.onMouseOver(this.props.linkData.source, this.props.linkData.target, evt);
        };
        this.handleOnMouseOut = evt => {
            this.props.onMouseOut(this.props.linkData.source, this.props.linkData.target, evt);
        };
    }
    componentDidMount() {
        this.applyOpacity(1, this.props.transitionDuration);
    }
    componentWillLeave(done) {
        this.applyOpacity(0, this.props.transitionDuration, done);
    }
    applyOpacity(opacity, transitionDuration, done = () => { }) {
        if (this.props.enableLegacyTransitions) {
            select(this.linkRef)
                // @ts-ignore
                .transition()
                .duration(transitionDuration)
                .style('opacity', opacity)
                .on('end', done);
        }
        else {
            select(this.linkRef).style('opacity', opacity);
            done();
        }
    }
    drawStepPath(linkData, orientation) {
        const { source, target } = linkData;
        const deltaY = target.y - source.y;
        return orientation === 'horizontal'
            ? `M${source.y},${source.x} H${source.y + deltaY / 2} V${target.x} H${target.y}`
            : `M${source.x},${source.y} V${source.y + deltaY / 2} H${target.x} V${target.y}`;
    }
    drawDiagonalPath(linkData, orientation) {
        const { source, target } = linkData;
        return orientation === 'horizontal'
            ? linkHorizontal()({
                source: [source.y, source.x],
                target: [target.y, target.x],
            })
            : linkVertical()({
                source: [source.x, source.y],
                target: [target.x, target.y],
            });
    }
    drawStraightPath(linkData, orientation) {
        const { source, target } = linkData;
        return orientation === 'horizontal'
            ? `M${source.y},${source.x}L${target.y},${target.x}`
            : `M${source.x},${source.y}L${target.x},${target.y}`;
    }
    drawElbowPath(linkData, orientation) {
        return orientation === 'horizontal'
            ? `M${linkData.source.y},${linkData.source.x}V${linkData.target.x}H${linkData.target.y}`
            : `M${linkData.source.x},${linkData.source.y}V${linkData.target.y}H${linkData.target.x}`;
    }
    drawPath() {
        const { linkData, orientation, pathFunc } = this.props;
        if (typeof pathFunc === 'function') {
            return pathFunc(linkData, orientation);
        }
        if (pathFunc === 'elbow') {
            return this.drawElbowPath(linkData, orientation);
        }
        if (pathFunc === 'straight') {
            return this.drawStraightPath(linkData, orientation);
        }
        if (pathFunc === 'step') {
            return this.drawStepPath(linkData, orientation);
        }
        return this.drawDiagonalPath(linkData, orientation);
    }
    getClassNames() {
        const { linkData, orientation, pathClassFunc } = this.props;
        const classNames = ['rd3t-link'];
        if (typeof pathClassFunc === 'function') {
            classNames.push(pathClassFunc(linkData, orientation));
        }
        return classNames.join(' ').trim();
    }
    render() {
        const { linkData } = this.props;
        return (React__default.createElement("path", { ref: l => {
                this.linkRef = l;
            }, style: Object.assign({}, this.state.initialStyle), className: this.getClassNames(), d: this.drawPath(), onClick: this.handleOnClick, onMouseOver: this.handleOnMouseOver, onMouseOut: this.handleOnMouseOut, "data-source-id": linkData.source.id, "data-target-id": linkData.target.id }));
    }
}

// Importing CSS files globally (e.g. `import "./styles.css"`) can cause resolution issues with certain
// libraries/frameworks.
// Example: Next.js (https://github.com/vercel/next.js/blob/master/errors/css-npm.md)
//
// Since rd3t's CSS is bare bones to begin with, we provide all required styles as a template string,
// which can be imported like any other TS/JS module and inlined into a `<style></style>` tag.
var globalCss = `
/* Tree */
.rd3t-tree-container {
  width: 100%;
  height: 100%;
}

.rd3t-grabbable {
  cursor: move; /* fallback if grab cursor is unsupported */
  cursor: grab;
  cursor: -moz-grab;
  cursor: -webkit-grab;
}
.rd3t-grabbable:active {
    cursor: grabbing;
    cursor: -moz-grabbing;
    cursor: -webkit-grabbing;
}

/* Node */
.rd3t-node {
  cursor: pointer;
  fill: #777;
  stroke: #000;
  stroke-width: 2;
}

.rd3t-leaf-node {
  cursor: pointer;
  fill: transparent;
  stroke: #000;
  stroke-width: 1;
}

.rd3t-label__title {
  fill: #000;
  stroke: none;
  font-weight: bolder;
}

.rd3t-label__attributes {
  fill: #777;
  stroke: none;
  font-weight: bolder;
  font-size: smaller;
}

/* Link */
.rd3t-link {
  fill: none;
  stroke: #000;
}
`;

class Tree extends React__default.Component {
    constructor() {
        super(...arguments);
        this.state = {
            dataRef: this.props.data,
            data: Tree.assignInternalProperties(clone(this.props.data)),
            d3: Tree.calculateD3Geometry(this.props),
            isTransitioning: false,
            isInitialRenderForDataset: true,
            dataKey: this.props.dataKey,
        };
        this.internalState = {
            targetNode: null,
            isTransitioning: false,
        };
        this.svgInstanceRef = `rd3t-svg-${v4()}`;
        this.gInstanceRef = `rd3t-g-${v4()}`;
        /**
         * Finds the node matching `nodeId` and
         * expands/collapses it, depending on the current state of
         * its internal `collapsed` property.
         * `setState` callback receives targetNode and handles
         * `props.onClick` if defined.
         */
        this.handleNodeToggle = (nodeId) => {
            const data = clone(this.state.data);
            const matches = this.findNodesById(nodeId, data, []);
            const targetNodeDatum = matches[0];
            if (this.props.collapsible && !this.state.isTransitioning) {
                if (targetNodeDatum.__rd3t.collapsed) {
                    Tree.expandNode(targetNodeDatum);
                    this.props.shouldCollapseNeighborNodes && this.collapseNeighborNodes(targetNodeDatum, data);
                }
                else {
                    Tree.collapseNode(targetNodeDatum);
                }
                if (this.props.enableLegacyTransitions) {
                    // Lock node toggling while transition takes place.
                    this.setState({ data, isTransitioning: true });
                    // Await transitionDuration + 10 ms before unlocking node toggling again.
                    setTimeout(() => this.setState({ isTransitioning: false }), this.props.transitionDuration + 10);
                }
                else {
                    this.setState({ data });
                }
                this.internalState.targetNode = targetNodeDatum;
            }
        };
        this.handleAddChildrenToNode = (nodeId, childrenData) => {
            const data = clone(this.state.data);
            const matches = this.findNodesById(nodeId, data, []);
            if (matches.length > 0) {
                const targetNodeDatum = matches[0];
                const depth = targetNodeDatum.__rd3t.depth;
                const formattedChildren = clone(childrenData).map((node) => Tree.assignInternalProperties([node], depth + 1));
                targetNodeDatum.children.push(...formattedChildren.flat());
                this.setState({ data });
            }
        };
        /**
         * Handles the user-defined `onNodeClick` function.
         */
        this.handleOnNodeClickCb = (hierarchyPointNode, evt) => {
            const { onNodeClick } = this.props;
            if (onNodeClick && typeof onNodeClick === 'function') {
                // Persist the SyntheticEvent for downstream handling by users.
                evt.persist();
                onNodeClick(clone(hierarchyPointNode), evt);
            }
        };
        /**
         * Handles the user-defined `onLinkClick` function.
         */
        this.handleOnLinkClickCb = (linkSource, linkTarget, evt) => {
            const { onLinkClick } = this.props;
            if (onLinkClick && typeof onLinkClick === 'function') {
                // Persist the SyntheticEvent for downstream handling by users.
                evt.persist();
                onLinkClick(clone(linkSource), clone(linkTarget), evt);
            }
        };
        /**
         * Handles the user-defined `onNodeMouseOver` function.
         */
        this.handleOnNodeMouseOverCb = (hierarchyPointNode, evt) => {
            const { onNodeMouseOver } = this.props;
            if (onNodeMouseOver && typeof onNodeMouseOver === 'function') {
                // Persist the SyntheticEvent for downstream handling by users.
                evt.persist();
                onNodeMouseOver(clone(hierarchyPointNode), evt);
            }
        };
        /**
         * Handles the user-defined `onLinkMouseOver` function.
         */
        this.handleOnLinkMouseOverCb = (linkSource, linkTarget, evt) => {
            const { onLinkMouseOver } = this.props;
            if (onLinkMouseOver && typeof onLinkMouseOver === 'function') {
                // Persist the SyntheticEvent for downstream handling by users.
                evt.persist();
                onLinkMouseOver(clone(linkSource), clone(linkTarget), evt);
            }
        };
        /**
         * Handles the user-defined `onNodeMouseOut` function.
         */
        this.handleOnNodeMouseOutCb = (hierarchyPointNode, evt) => {
            const { onNodeMouseOut } = this.props;
            if (onNodeMouseOut && typeof onNodeMouseOut === 'function') {
                // Persist the SyntheticEvent for downstream handling by users.
                evt.persist();
                onNodeMouseOut(clone(hierarchyPointNode), evt);
            }
        };
        /**
         * Handles the user-defined `onLinkMouseOut` function.
         */
        this.handleOnLinkMouseOutCb = (linkSource, linkTarget, evt) => {
            const { onLinkMouseOut } = this.props;
            if (onLinkMouseOut && typeof onLinkMouseOut === 'function') {
                // Persist the SyntheticEvent for downstream handling by users.
                evt.persist();
                onLinkMouseOut(clone(linkSource), clone(linkTarget), evt);
            }
        };
        /**
         * Takes a hierarchy point node and centers the node on the screen
         * if the dimensions parameter is passed to `Tree`.
         *
         * This code is adapted from Rob Schmuecker's centerNode method.
         * Link: http://bl.ocks.org/robschmuecker/7880033
         */
        this.centerNode = (hierarchyPointNode) => {
            const { dimensions, orientation, zoom, centeringTransitionDuration } = this.props;
            if (dimensions) {
                const g = select(`.${this.gInstanceRef}`);
                const svg = select(`.${this.svgInstanceRef}`);
                const scale = this.state.d3.scale;
                let x;
                let y;
                // if the orientation is horizontal, calculate the variables inverted (x->y, y->x)
                if (orientation === 'horizontal') {
                    y = -hierarchyPointNode.x * scale + dimensions.height / 2;
                    x = -hierarchyPointNode.y * scale + dimensions.width / 2;
                }
                else {
                    // else, calculate the variables normally (x->x, y->y)
                    x = -hierarchyPointNode.x * scale + dimensions.width / 2;
                    y = -hierarchyPointNode.y * scale + dimensions.height / 2;
                }
                //@ts-ignore
                g.transition()
                    .duration(centeringTransitionDuration)
                    .attr('transform', 'translate(' + x + ',' + y + ')scale(' + scale + ')');
                // Sets the viewport to the new center so that it does not jump back to original
                // coordinates when dragged/zoomed
                //@ts-ignore
                svg.call(d3zoom().transform, identity.translate(x, y).scale(zoom));
            }
        };
        /**
         * Determines which additional `className` prop should be passed to the node & returns it.
         */
        this.getNodeClassName = (parent, nodeDatum) => {
            const { rootNodeClassName, branchNodeClassName, leafNodeClassName } = this.props;
            const hasParent = parent !== null && parent !== undefined;
            if (hasParent) {
                return nodeDatum.children ? branchNodeClassName : leafNodeClassName;
            }
            else {
                return rootNodeClassName;
            }
        };
    }
    static getDerivedStateFromProps(nextProps, prevState) {
        let derivedState = null;
        // Clone new data & assign internal properties if `data` object reference changed.
        // If the dataKey was present but didn't change, then we don't need to re-render the tree
        const dataKeyChanged = !nextProps.dataKey || prevState.dataKey !== nextProps.dataKey;
        if (nextProps.data !== prevState.dataRef && dataKeyChanged) {
            derivedState = {
                dataRef: nextProps.data,
                data: Tree.assignInternalProperties(clone(nextProps.data)),
                isInitialRenderForDataset: true,
                dataKey: nextProps.dataKey,
            };
        }
        const d3 = Tree.calculateD3Geometry(nextProps);
        if (!dequal(d3, prevState.d3)) {
            derivedState = derivedState || {};
            derivedState.d3 = d3;
        }
        return derivedState;
    }
    componentDidMount() {
        this.bindZoomListener(this.props);
        this.setState({ isInitialRenderForDataset: false });
    }
    componentDidUpdate(prevProps) {
        if (this.props.data !== prevProps.data) {
            // If last `render` was due to change in dataset -> mark the initial render as done.
            this.setState({ isInitialRenderForDataset: false });
        }
        if (!dequal(this.props.translate, prevProps.translate) ||
            !dequal(this.props.scaleExtent, prevProps.scaleExtent) ||
            this.props.zoomable !== prevProps.zoomable ||
            this.props.draggable !== prevProps.draggable ||
            this.props.zoom !== prevProps.zoom ||
            this.props.enableLegacyTransitions !== prevProps.enableLegacyTransitions) {
            // If zoom-specific props change -> rebind listener with new values.
            // Or: rebind zoom listeners to new DOM nodes in case legacy transitions were enabled/disabled.
            this.bindZoomListener(this.props);
        }
        if (typeof this.props.onUpdate === 'function') {
            this.props.onUpdate({
                node: this.internalState.targetNode ? clone(this.internalState.targetNode) : null,
                zoom: this.state.d3.scale,
                translate: this.state.d3.translate,
            });
        }
        // Reset the last target node after we've flushed it to `onUpdate`.
        this.internalState.targetNode = null;
    }
    /**
     * Collapses all tree nodes with a `depth` larger than `initialDepth`.
     *
     * @param {array} nodeSet Array of nodes generated by `generateTree`
     * @param {number} initialDepth Maximum initial depth the tree should render
     */
    setInitialTreeDepth(nodeSet, initialDepth) {
        nodeSet.forEach(n => {
            n.data.__rd3t.collapsed = n.depth >= initialDepth;
        });
    }
    /**
     * bindZoomListener - If `props.zoomable`, binds a listener for
     * "zoom" events to the SVG and sets scaleExtent to min/max
     * specified in `props.scaleExtent`.
     */
    bindZoomListener(props) {
        const { zoomable, scaleExtent, translate, zoom, onUpdate, hasInteractiveNodes } = props;
        const svg = select(`.${this.svgInstanceRef}`);
        const g = select(`.${this.gInstanceRef}`);
        // Sets initial offset, so that first pan and zoom does not jump back to default [0,0] coords.
        // @ts-ignore
        svg.call(d3zoom().transform, identity.translate(translate.x, translate.y).scale(zoom));
        svg.call(d3zoom()
            .scaleExtent(zoomable ? [scaleExtent.min, scaleExtent.max] : [zoom, zoom])
            // TODO: break this out into a separate zoom handler fn, rather than inlining it.
            .filter((event) => {
            if (hasInteractiveNodes) {
                return (event.target.classList.contains(this.svgInstanceRef) ||
                    event.target.classList.contains(this.gInstanceRef) ||
                    event.shiftKey);
            }
            return true;
        })
            .on('zoom', (event) => {
            if (!this.props.draggable &&
                ['mousemove', 'touchmove', 'dblclick'].includes(event.sourceEvent.type)) {
                return;
            }
            g.attr('transform', event.transform);
            if (typeof onUpdate === 'function') {
                // This callback is magically called not only on "zoom", but on "drag", as well,
                // even though event.type == "zoom".
                // Taking advantage of this and not writing a "drag" handler.
                onUpdate({
                    node: null,
                    zoom: event.transform.k,
                    translate: { x: event.transform.x, y: event.transform.y },
                });
                // TODO: remove this? Shouldn't be mutating state keys directly.
                this.state.d3.scale = event.transform.k;
                this.state.d3.translate = {
                    x: event.transform.x,
                    y: event.transform.y,
                };
            }
        }));
    }
    /**
     * Assigns internal properties that are required for tree
     * manipulation to each node in the `data` set and returns a new `data` array.
     *
     * @static
     */
    static assignInternalProperties(data, currentDepth = 0) {
        // Wrap the root node into an array for recursive transformations if it wasn't in one already.
        const d = Array.isArray(data) ? data : [data];
        return d.map(n => {
            const nodeDatum = n;
            nodeDatum.__rd3t = { id: null, depth: null, collapsed: false };
            nodeDatum.__rd3t.id = v4();
            // D3@v5 compat: manually assign `depth` to node.data so we don't have
            // to hold full node+link sets in state.
            // TODO: avoid this extra step by checking D3's node.depth directly.
            nodeDatum.__rd3t.depth = currentDepth;
            // If there are children, recursively assign properties to them too.
            if (nodeDatum.children && nodeDatum.children.length > 0) {
                nodeDatum.children = Tree.assignInternalProperties(nodeDatum.children, currentDepth + 1);
            }
            return nodeDatum;
        });
    }
    /**
     * Recursively walks the nested `nodeSet` until a node matching `nodeId` is found.
     */
    findNodesById(nodeId, nodeSet, hits) {
        if (hits.length > 0) {
            return hits;
        }
        hits = hits.concat(nodeSet.filter(node => node.__rd3t.id === nodeId));
        nodeSet.forEach(node => {
            if (node.children && node.children.length > 0) {
                hits = this.findNodesById(nodeId, node.children, hits);
            }
        });
        return hits;
    }
    /**
     * Recursively walks the nested `nodeSet` until all nodes at `depth` have been found.
     *
     * @param {number} depth Target depth for which nodes should be returned
     * @param {array} nodeSet Array of nested `node` objects
     * @param {array} accumulator Accumulator for matches, passed between recursive calls
     */
    findNodesAtDepth(depth, nodeSet, accumulator) {
        accumulator = accumulator.concat(nodeSet.filter(node => node.__rd3t.depth === depth));
        nodeSet.forEach(node => {
            if (node.children && node.children.length > 0) {
                accumulator = this.findNodesAtDepth(depth, node.children, accumulator);
            }
        });
        return accumulator;
    }
    /**
     * Recursively sets the internal `collapsed` property of
     * the passed `TreeNodeDatum` and its children to `true`.
     *
     * @static
     */
    static collapseNode(nodeDatum) {
        nodeDatum.__rd3t.collapsed = true;
        if (nodeDatum.children && nodeDatum.children.length > 0) {
            nodeDatum.children.forEach(child => {
                Tree.collapseNode(child);
            });
        }
    }
    /**
     * Sets the internal `collapsed` property of
     * the passed `TreeNodeDatum` object to `false`.
     *
     * @static
     */
    static expandNode(nodeDatum) {
        nodeDatum.__rd3t.collapsed = false;
    }
    /**
     * Collapses all nodes in `nodeSet` that are neighbors (same depth) of `targetNode`.
     */
    collapseNeighborNodes(targetNode, nodeSet) {
        const neighbors = this.findNodesAtDepth(targetNode.__rd3t.depth, nodeSet, []).filter(node => node.__rd3t.id !== targetNode.__rd3t.id);
        neighbors.forEach(neighbor => Tree.collapseNode(neighbor));
    }
    /**
     * Generates tree elements (`nodes` and `links`) by
     * grabbing the rootNode from `this.state.data[0]`.
     * Restricts tree depth to `props.initialDepth` if defined and if this is
     * the initial render of the tree.
     */
    generateTree() {
        const { initialDepth, depthFactor, separation, nodeSize, orientation } = this.props;
        const { isInitialRenderForDataset } = this.state;
        const tree = d3tree()
            .nodeSize(orientation === 'horizontal' ? [nodeSize.y, nodeSize.x] : [nodeSize.x, nodeSize.y])
            .separation((a, b) => a.parent.data.__rd3t.id === b.parent.data.__rd3t.id
            ? separation.siblings
            : separation.nonSiblings);
        const rootNode = tree(hierarchy(this.state.data[0], d => (d.__rd3t.collapsed ? null : d.children)));
        let nodes = rootNode.descendants();
        const links = rootNode.links();
        // Configure nodes' `collapsed` property on first render if `initialDepth` is defined.
        if (initialDepth !== undefined && isInitialRenderForDataset) {
            this.setInitialTreeDepth(nodes, initialDepth);
        }
        if (depthFactor) {
            nodes.forEach(node => {
                node.y = node.depth * depthFactor;
            });
        }
        return { nodes, links };
    }
    /**
     * Set initial zoom and position.
     * Also limit zoom level according to `scaleExtent` on initial display. This is necessary,
     * because the first time we are setting it as an SVG property, instead of going
     * through D3's scaling mechanism, which would have picked up both properties.
     *
     * @static
     */
    static calculateD3Geometry(nextProps) {
        let scale;
        if (nextProps.zoom > nextProps.scaleExtent.max) {
            scale = nextProps.scaleExtent.max;
        }
        else if (nextProps.zoom < nextProps.scaleExtent.min) {
            scale = nextProps.scaleExtent.min;
        }
        else {
            scale = nextProps.zoom;
        }
        return {
            translate: nextProps.translate,
            scale,
        };
    }
    render() {
        const { nodes, links } = this.generateTree();
        const { renderCustomNodeElement, orientation, pathFunc, transitionDuration, nodeSize, depthFactor, initialDepth, separation, enableLegacyTransitions, svgClassName, pathClassFunc, } = this.props;
        const { translate, scale } = this.state.d3;
        const subscriptions = Object.assign(Object.assign(Object.assign({}, nodeSize), separation), { depthFactor,
            initialDepth });
        return (React__default.createElement("div", { className: "rd3t-tree-container rd3t-grabbable" },
            React__default.createElement("style", null, globalCss),
            React__default.createElement("svg", { className: `rd3t-svg ${this.svgInstanceRef} ${svgClassName}`, width: "100%", height: "100%" },
                React__default.createElement(TransitionGroupWrapper, { enableLegacyTransitions: enableLegacyTransitions, component: "g", className: `rd3t-g ${this.gInstanceRef}`, transform: `translate(${translate.x},${translate.y}) scale(${scale})` },
                    links.map((linkData, i) => {
                        return (React__default.createElement(Link, { key: 'link-' + i, orientation: orientation, pathFunc: pathFunc, pathClassFunc: pathClassFunc, linkData: linkData, onClick: this.handleOnLinkClickCb, onMouseOver: this.handleOnLinkMouseOverCb, onMouseOut: this.handleOnLinkMouseOutCb, enableLegacyTransitions: enableLegacyTransitions, transitionDuration: transitionDuration }));
                    }),
                    nodes.map((hierarchyPointNode, i) => {
                        const { data, x, y, parent } = hierarchyPointNode;
                        return (React__default.createElement(Node, { key: 'node-' + i, data: data, position: { x, y }, hierarchyPointNode: hierarchyPointNode, parent: parent, nodeClassName: this.getNodeClassName(parent, data), renderCustomNodeElement: renderCustomNodeElement, nodeSize: nodeSize, orientation: orientation, enableLegacyTransitions: enableLegacyTransitions, transitionDuration: transitionDuration, onNodeToggle: this.handleNodeToggle, onNodeClick: this.handleOnNodeClickCb, onNodeMouseOver: this.handleOnNodeMouseOverCb, onNodeMouseOut: this.handleOnNodeMouseOutCb, handleAddChildrenToNode: this.handleAddChildrenToNode, subscriptions: subscriptions, centerNode: this.centerNode }));
                    })))));
    }
}
Tree.defaultProps = {
    onNodeClick: undefined,
    onNodeMouseOver: undefined,
    onNodeMouseOut: undefined,
    onLinkClick: undefined,
    onLinkMouseOver: undefined,
    onLinkMouseOut: undefined,
    onUpdate: undefined,
    orientation: 'horizontal',
    translate: { x: 0, y: 0 },
    pathFunc: 'diagonal',
    pathClassFunc: undefined,
    transitionDuration: 500,
    depthFactor: undefined,
    collapsible: true,
    initialDepth: undefined,
    zoomable: true,
    draggable: true,
    zoom: 1,
    scaleExtent: { min: 0.1, max: 1 },
    nodeSize: { x: 140, y: 140 },
    separation: { siblings: 1, nonSiblings: 2 },
    shouldCollapseNeighborNodes: false,
    svgClassName: '',
    rootNodeClassName: '',
    branchNodeClassName: '',
    leafNodeClassName: '',
    renderCustomNodeElement: undefined,
    enableLegacyTransitions: false,
    hasInteractiveNodes: false,
    dimensions: undefined,
    centeringTransitionDuration: 800,
    dataKey: undefined,
};

function treeToData(tree) {
    var _a = tree.node, label = _a.label, length = _a.length, children = _a.children;
    if (!Array.isArray(children)) {
        throw new Error("Children are not an array");
    }
    if (children.length == 0) {
        return {
            name: 'node',
            length: length,
            label: label
        };
    }
    else {
        var childrenAsTrees = children.map(treeToData);
        return {
            name: 'node',
            length: length,
            label: label,
            children: childrenAsTrees
        };
    }
}
function renderForeignObjectNode(_a, _, foreignObjectProps) {
    var _b;
    var nodeDatum = _a.nodeDatum;
    var nodeDatum_ = nodeDatum;
    var width = 10 * ((_b = nodeDatum_.length) !== null && _b !== void 0 ? _b : 10);
    return (jsxs("g", { children: [jsx("rect", { x: "-50", y: "-10", width: width, height: "20", fill: "green", style: { border: "black" } }), jsx("foreignObject", __assign({}, foreignObjectProps, { width: width, style: { textAlign: "center" } }, { children: nodeDatum_.label && jsx(InteractiveCode, { fmt: nodeDatum_.label }) }))] }));
}
function centerTree(r, t, setT) {
    React.useLayoutEffect(function () {
        var elt = r.current;
        if (elt == null) {
            return;
        }
        if (t != null) {
            return;
        }
        var b = elt.getBoundingClientRect();
        if (!b.width || !b.height) {
            return;
        }
        setT({ x: b.width / 2, y: 20 });
    });
}
function RenderDisplayTree(_a) {
    var pos = _a.pos, tree = _a.tree, r = _a.r;
    var nodeSize = { x: 120, y: 40 };
    var foreignObjectProps = { width: 100, height: 30, y: -10, x: -50 };
    var _b = React.useState(null), t = _b[0], setT = _b[1];
    centerTree(r, t, setT);
    return (jsx(Tree, { data: treeToData(tree), translate: t !== null && t !== void 0 ? t : { x: 0, y: 0 }, nodeSize: nodeSize, renderCustomNodeElement: function (rd3tProps) {
            return renderForeignObjectNode(rd3tProps, pos, foreignObjectProps);
        }, orientation: 'vertical', pathFunc: 'straight' }));
}
function RenderDisplay(props) {
    var pos = props.pos;
    var _a = React.useState([]), selectedLocs = _a[0], setSelectedLocs = _a[1];
    var locs = React.useMemo(function () { return ({
        isSelected: function (l) { return selectedLocs.some(function (v) { return GoalsLocation.isEqual(v, l); }); },
        setSelected: function (l, act) { return setSelectedLocs(function (ls) {
            // We ensure that `selectedLocs` maintains its reference identity if the selection
            // status of `l` didn't change.
            var newLocs = ls.filter(function (v) { return !GoalsLocation.isEqual(v, l); });
            var wasSelected = newLocs.length !== ls.length;
            var isSelected = typeof act === 'function' ? act(wasSelected) : act;
            if (isSelected)
                newLocs.push(l);
            return wasSelected === isSelected ? ls : newLocs;
        }); },
        subexprTemplate: { mvarId: '', loc: { target: '' } }
    }); }, [selectedLocs]);
    props.selectedLocations = selectedLocs;
    React.useEffect(function () { return setSelectedLocs([]); }, [pos.uri, pos.line, pos.character]);
    var r = React.useRef(null);
    return (jsxs("div", __assign({ style: {
            height: '400px',
            display: 'inline-flex',
            minWidth: '600px',
            border: '1px solid rgba(100, 100, 100, 0.2)',
            overflow: 'hidden',
            resize: 'both',
            opacity: '0.9',
        }, ref: r }, { children: [jsx(LocationsContext.Provider, __assign({ value: locs }, { children: jsx(RenderDisplayTree, { pos: pos, tree: props.tree, r: r }) })), jsx("div", { children: selectedLocs.map(function (loc) { console.log(loc); return jsx("p", { children: "Location selected" }); }) })] })));
}

export { RenderDisplayTree, RenderDisplay as default };
//# sourceMappingURL=data:application/json;charset=utf-8;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoiaW50ZXJhY3RpdmVUcmVlRGlzcGxheS5qcyIsInNvdXJjZXMiOlsiLi4vLi4vd2lkZ2V0L25vZGVfbW9kdWxlcy90c2xpYi90c2xpYi5lczYuanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL2QzLWhpZXJhcmNoeS9zcmMvaGllcmFyY2h5L2NvdW50LmpzIiwiLi4vLi4vd2lkZ2V0L25vZGVfbW9kdWxlcy9kMy1oaWVyYXJjaHkvc3JjL2hpZXJhcmNoeS9lYWNoLmpzIiwiLi4vLi4vd2lkZ2V0L25vZGVfbW9kdWxlcy9kMy1oaWVyYXJjaHkvc3JjL2hpZXJhcmNoeS9lYWNoQmVmb3JlLmpzIiwiLi4vLi4vd2lkZ2V0L25vZGVfbW9kdWxlcy9kMy1oaWVyYXJjaHkvc3JjL2hpZXJhcmNoeS9lYWNoQWZ0ZXIuanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL2QzLWhpZXJhcmNoeS9zcmMvaGllcmFyY2h5L3N1bS5qcyIsIi4uLy4uL3dpZGdldC9ub2RlX21vZHVsZXMvZDMtaGllcmFyY2h5L3NyYy9oaWVyYXJjaHkvc29ydC5qcyIsIi4uLy4uL3dpZGdldC9ub2RlX21vZHVsZXMvZDMtaGllcmFyY2h5L3NyYy9oaWVyYXJjaHkvcGF0aC5qcyIsIi4uLy4uL3dpZGdldC9ub2RlX21vZHVsZXMvZDMtaGllcmFyY2h5L3NyYy9oaWVyYXJjaHkvYW5jZXN0b3JzLmpzIiwiLi4vLi4vd2lkZ2V0L25vZGVfbW9kdWxlcy9kMy1oaWVyYXJjaHkvc3JjL2hpZXJhcmNoeS9kZXNjZW5kYW50cy5qcyIsIi4uLy4uL3dpZGdldC9ub2RlX21vZHVsZXMvZDMtaGllcmFyY2h5L3NyYy9oaWVyYXJjaHkvbGVhdmVzLmpzIiwiLi4vLi4vd2lkZ2V0L25vZGVfbW9kdWxlcy9kMy1oaWVyYXJjaHkvc3JjL2hpZXJhcmNoeS9saW5rcy5qcyIsIi4uLy4uL3dpZGdldC9ub2RlX21vZHVsZXMvZDMtaGllcmFyY2h5L3NyYy9oaWVyYXJjaHkvaW5kZXguanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL2QzLWhpZXJhcmNoeS9zcmMvdHJlZS5qcyIsIi4uLy4uL3dpZGdldC9ub2RlX21vZHVsZXMvZDMtc2VsZWN0aW9uL3NyYy9uYW1lc3BhY2VzLmpzIiwiLi4vLi4vd2lkZ2V0L25vZGVfbW9kdWxlcy9kMy1zZWxlY3Rpb24vc3JjL25hbWVzcGFjZS5qcyIsIi4uLy4uL3dpZGdldC9ub2RlX21vZHVsZXMvZDMtc2VsZWN0aW9uL3NyYy9jcmVhdG9yLmpzIiwiLi4vLi4vd2lkZ2V0L25vZGVfbW9kdWxlcy9kMy1zZWxlY3Rpb24vc3JjL3NlbGVjdG9yLmpzIiwiLi4vLi4vd2lkZ2V0L25vZGVfbW9kdWxlcy9kMy1zZWxlY3Rpb24vc3JjL3NlbGVjdGlvbi9zZWxlY3QuanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL2QzLXNlbGVjdGlvbi9zcmMvYXJyYXkuanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL2QzLXNlbGVjdGlvbi9zcmMvc2VsZWN0b3JBbGwuanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL2QzLXNlbGVjdGlvbi9zcmMvc2VsZWN0aW9uL3NlbGVjdEFsbC5qcyIsIi4uLy4uL3dpZGdldC9ub2RlX21vZHVsZXMvZDMtc2VsZWN0aW9uL3NyYy9tYXRjaGVyLmpzIiwiLi4vLi4vd2lkZ2V0L25vZGVfbW9kdWxlcy9kMy1zZWxlY3Rpb24vc3JjL3NlbGVjdGlvbi9zZWxlY3RDaGlsZC5qcyIsIi4uLy4uL3dpZGdldC9ub2RlX21vZHVsZXMvZDMtc2VsZWN0aW9uL3NyYy9zZWxlY3Rpb24vc2VsZWN0Q2hpbGRyZW4uanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL2QzLXNlbGVjdGlvbi9zcmMvc2VsZWN0aW9uL2ZpbHRlci5qcyIsIi4uLy4uL3dpZGdldC9ub2RlX21vZHVsZXMvZDMtc2VsZWN0aW9uL3NyYy9zZWxlY3Rpb24vc3BhcnNlLmpzIiwiLi4vLi4vd2lkZ2V0L25vZGVfbW9kdWxlcy9kMy1zZWxlY3Rpb24vc3JjL3NlbGVjdGlvbi9lbnRlci5qcyIsIi4uLy4uL3dpZGdldC9ub2RlX21vZHVsZXMvZDMtc2VsZWN0aW9uL3NyYy9jb25zdGFudC5qcyIsIi4uLy4uL3dpZGdldC9ub2RlX21vZHVsZXMvZDMtc2VsZWN0aW9uL3NyYy9zZWxlY3Rpb24vZGF0YS5qcyIsIi4uLy4uL3dpZGdldC9ub2RlX21vZHVsZXMvZDMtc2VsZWN0aW9uL3NyYy9zZWxlY3Rpb24vZXhpdC5qcyIsIi4uLy4uL3dpZGdldC9ub2RlX21vZHVsZXMvZDMtc2VsZWN0aW9uL3NyYy9zZWxlY3Rpb24vam9pbi5qcyIsIi4uLy4uL3dpZGdldC9ub2RlX21vZHVsZXMvZDMtc2VsZWN0aW9uL3NyYy9zZWxlY3Rpb24vbWVyZ2UuanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL2QzLXNlbGVjdGlvbi9zcmMvc2VsZWN0aW9uL29yZGVyLmpzIiwiLi4vLi4vd2lkZ2V0L25vZGVfbW9kdWxlcy9kMy1zZWxlY3Rpb24vc3JjL3NlbGVjdGlvbi9zb3J0LmpzIiwiLi4vLi4vd2lkZ2V0L25vZGVfbW9kdWxlcy9kMy1zZWxlY3Rpb24vc3JjL3NlbGVjdGlvbi9jYWxsLmpzIiwiLi4vLi4vd2lkZ2V0L25vZGVfbW9kdWxlcy9kMy1zZWxlY3Rpb24vc3JjL3NlbGVjdGlvbi9ub2Rlcy5qcyIsIi4uLy4uL3dpZGdldC9ub2RlX21vZHVsZXMvZDMtc2VsZWN0aW9uL3NyYy9zZWxlY3Rpb24vbm9kZS5qcyIsIi4uLy4uL3dpZGdldC9ub2RlX21vZHVsZXMvZDMtc2VsZWN0aW9uL3NyYy9zZWxlY3Rpb24vc2l6ZS5qcyIsIi4uLy4uL3dpZGdldC9ub2RlX21vZHVsZXMvZDMtc2VsZWN0aW9uL3NyYy9zZWxlY3Rpb24vZW1wdHkuanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL2QzLXNlbGVjdGlvbi9zcmMvc2VsZWN0aW9uL2VhY2guanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL2QzLXNlbGVjdGlvbi9zcmMvc2VsZWN0aW9uL2F0dHIuanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL2QzLXNlbGVjdGlvbi9zcmMvd2luZG93LmpzIiwiLi4vLi4vd2lkZ2V0L25vZGVfbW9kdWxlcy9kMy1zZWxlY3Rpb24vc3JjL3NlbGVjdGlvbi9zdHlsZS5qcyIsIi4uLy4uL3dpZGdldC9ub2RlX21vZHVsZXMvZDMtc2VsZWN0aW9uL3NyYy9zZWxlY3Rpb24vcHJvcGVydHkuanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL2QzLXNlbGVjdGlvbi9zcmMvc2VsZWN0aW9uL2NsYXNzZWQuanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL2QzLXNlbGVjdGlvbi9zcmMvc2VsZWN0aW9uL3RleHQuanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL2QzLXNlbGVjdGlvbi9zcmMvc2VsZWN0aW9uL2h0bWwuanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL2QzLXNlbGVjdGlvbi9zcmMvc2VsZWN0aW9uL3JhaXNlLmpzIiwiLi4vLi4vd2lkZ2V0L25vZGVfbW9kdWxlcy9kMy1zZWxlY3Rpb24vc3JjL3NlbGVjdGlvbi9sb3dlci5qcyIsIi4uLy4uL3dpZGdldC9ub2RlX21vZHVsZXMvZDMtc2VsZWN0aW9uL3NyYy9zZWxlY3Rpb24vYXBwZW5kLmpzIiwiLi4vLi4vd2lkZ2V0L25vZGVfbW9kdWxlcy9kMy1zZWxlY3Rpb24vc3JjL3NlbGVjdGlvbi9pbnNlcnQuanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL2QzLXNlbGVjdGlvbi9zcmMvc2VsZWN0aW9uL3JlbW92ZS5qcyIsIi4uLy4uL3dpZGdldC9ub2RlX21vZHVsZXMvZDMtc2VsZWN0aW9uL3NyYy9zZWxlY3Rpb24vY2xvbmUuanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL2QzLXNlbGVjdGlvbi9zcmMvc2VsZWN0aW9uL2RhdHVtLmpzIiwiLi4vLi4vd2lkZ2V0L25vZGVfbW9kdWxlcy9kMy1zZWxlY3Rpb24vc3JjL3NlbGVjdGlvbi9vbi5qcyIsIi4uLy4uL3dpZGdldC9ub2RlX21vZHVsZXMvZDMtc2VsZWN0aW9uL3NyYy9zZWxlY3Rpb24vZGlzcGF0Y2guanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL2QzLXNlbGVjdGlvbi9zcmMvc2VsZWN0aW9uL2l0ZXJhdG9yLmpzIiwiLi4vLi4vd2lkZ2V0L25vZGVfbW9kdWxlcy9kMy1zZWxlY3Rpb24vc3JjL3NlbGVjdGlvbi9pbmRleC5qcyIsIi4uLy4uL3dpZGdldC9ub2RlX21vZHVsZXMvZDMtc2VsZWN0aW9uL3NyYy9zZWxlY3QuanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL2QzLXNlbGVjdGlvbi9zcmMvc291cmNlRXZlbnQuanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL2QzLXNlbGVjdGlvbi9zcmMvcG9pbnRlci5qcyIsIi4uLy4uL3dpZGdldC9ub2RlX21vZHVsZXMvZDMtZGlzcGF0Y2gvc3JjL2Rpc3BhdGNoLmpzIiwiLi4vLi4vd2lkZ2V0L25vZGVfbW9kdWxlcy9kMy1kcmFnL3NyYy9ub2V2ZW50LmpzIiwiLi4vLi4vd2lkZ2V0L25vZGVfbW9kdWxlcy9kMy1kcmFnL3NyYy9ub2RyYWcuanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL2QzLWNvbG9yL3NyYy9kZWZpbmUuanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL2QzLWNvbG9yL3NyYy9jb2xvci5qcyIsIi4uLy4uL3dpZGdldC9ub2RlX21vZHVsZXMvZDMtaW50ZXJwb2xhdGUvc3JjL2NvbnN0YW50LmpzIiwiLi4vLi4vd2lkZ2V0L25vZGVfbW9kdWxlcy9kMy1pbnRlcnBvbGF0ZS9zcmMvY29sb3IuanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL2QzLWludGVycG9sYXRlL3NyYy9yZ2IuanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL2QzLWludGVycG9sYXRlL3NyYy9udW1iZXIuanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL2QzLWludGVycG9sYXRlL3NyYy9zdHJpbmcuanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL2QzLWludGVycG9sYXRlL3NyYy90cmFuc2Zvcm0vZGVjb21wb3NlLmpzIiwiLi4vLi4vd2lkZ2V0L25vZGVfbW9kdWxlcy9kMy1pbnRlcnBvbGF0ZS9zcmMvdHJhbnNmb3JtL3BhcnNlLmpzIiwiLi4vLi4vd2lkZ2V0L25vZGVfbW9kdWxlcy9kMy1pbnRlcnBvbGF0ZS9zcmMvdHJhbnNmb3JtL2luZGV4LmpzIiwiLi4vLi4vd2lkZ2V0L25vZGVfbW9kdWxlcy9kMy1pbnRlcnBvbGF0ZS9zcmMvem9vbS5qcyIsIi4uLy4uL3dpZGdldC9ub2RlX21vZHVsZXMvZDMtdGltZXIvc3JjL3RpbWVyLmpzIiwiLi4vLi4vd2lkZ2V0L25vZGVfbW9kdWxlcy9kMy10aW1lci9zcmMvdGltZW91dC5qcyIsIi4uLy4uL3dpZGdldC9ub2RlX21vZHVsZXMvZDMtdHJhbnNpdGlvbi9zcmMvdHJhbnNpdGlvbi9zY2hlZHVsZS5qcyIsIi4uLy4uL3dpZGdldC9ub2RlX21vZHVsZXMvZDMtdHJhbnNpdGlvbi9zcmMvaW50ZXJydXB0LmpzIiwiLi4vLi4vd2lkZ2V0L25vZGVfbW9kdWxlcy9kMy10cmFuc2l0aW9uL3NyYy9zZWxlY3Rpb24vaW50ZXJydXB0LmpzIiwiLi4vLi4vd2lkZ2V0L25vZGVfbW9kdWxlcy9kMy10cmFuc2l0aW9uL3NyYy90cmFuc2l0aW9uL3R3ZWVuLmpzIiwiLi4vLi4vd2lkZ2V0L25vZGVfbW9kdWxlcy9kMy10cmFuc2l0aW9uL3NyYy90cmFuc2l0aW9uL2ludGVycG9sYXRlLmpzIiwiLi4vLi4vd2lkZ2V0L25vZGVfbW9kdWxlcy9kMy10cmFuc2l0aW9uL3NyYy90cmFuc2l0aW9uL2F0dHIuanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL2QzLXRyYW5zaXRpb24vc3JjL3RyYW5zaXRpb24vYXR0clR3ZWVuLmpzIiwiLi4vLi4vd2lkZ2V0L25vZGVfbW9kdWxlcy9kMy10cmFuc2l0aW9uL3NyYy90cmFuc2l0aW9uL2RlbGF5LmpzIiwiLi4vLi4vd2lkZ2V0L25vZGVfbW9kdWxlcy9kMy10cmFuc2l0aW9uL3NyYy90cmFuc2l0aW9uL2R1cmF0aW9uLmpzIiwiLi4vLi4vd2lkZ2V0L25vZGVfbW9kdWxlcy9kMy10cmFuc2l0aW9uL3NyYy90cmFuc2l0aW9uL2Vhc2UuanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL2QzLXRyYW5zaXRpb24vc3JjL3RyYW5zaXRpb24vZWFzZVZhcnlpbmcuanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL2QzLXRyYW5zaXRpb24vc3JjL3RyYW5zaXRpb24vZmlsdGVyLmpzIiwiLi4vLi4vd2lkZ2V0L25vZGVfbW9kdWxlcy9kMy10cmFuc2l0aW9uL3NyYy90cmFuc2l0aW9uL21lcmdlLmpzIiwiLi4vLi4vd2lkZ2V0L25vZGVfbW9kdWxlcy9kMy10cmFuc2l0aW9uL3NyYy90cmFuc2l0aW9uL29uLmpzIiwiLi4vLi4vd2lkZ2V0L25vZGVfbW9kdWxlcy9kMy10cmFuc2l0aW9uL3NyYy90cmFuc2l0aW9uL3JlbW92ZS5qcyIsIi4uLy4uL3dpZGdldC9ub2RlX21vZHVsZXMvZDMtdHJhbnNpdGlvbi9zcmMvdHJhbnNpdGlvbi9zZWxlY3QuanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL2QzLXRyYW5zaXRpb24vc3JjL3RyYW5zaXRpb24vc2VsZWN0QWxsLmpzIiwiLi4vLi4vd2lkZ2V0L25vZGVfbW9kdWxlcy9kMy10cmFuc2l0aW9uL3NyYy90cmFuc2l0aW9uL3NlbGVjdGlvbi5qcyIsIi4uLy4uL3dpZGdldC9ub2RlX21vZHVsZXMvZDMtdHJhbnNpdGlvbi9zcmMvdHJhbnNpdGlvbi9zdHlsZS5qcyIsIi4uLy4uL3dpZGdldC9ub2RlX21vZHVsZXMvZDMtdHJhbnNpdGlvbi9zcmMvdHJhbnNpdGlvbi9zdHlsZVR3ZWVuLmpzIiwiLi4vLi4vd2lkZ2V0L25vZGVfbW9kdWxlcy9kMy10cmFuc2l0aW9uL3NyYy90cmFuc2l0aW9uL3RleHQuanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL2QzLXRyYW5zaXRpb24vc3JjL3RyYW5zaXRpb24vdGV4dFR3ZWVuLmpzIiwiLi4vLi4vd2lkZ2V0L25vZGVfbW9kdWxlcy9kMy10cmFuc2l0aW9uL3NyYy90cmFuc2l0aW9uL3RyYW5zaXRpb24uanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL2QzLXRyYW5zaXRpb24vc3JjL3RyYW5zaXRpb24vZW5kLmpzIiwiLi4vLi4vd2lkZ2V0L25vZGVfbW9kdWxlcy9kMy10cmFuc2l0aW9uL3NyYy90cmFuc2l0aW9uL2luZGV4LmpzIiwiLi4vLi4vd2lkZ2V0L25vZGVfbW9kdWxlcy9kMy1lYXNlL3NyYy9jdWJpYy5qcyIsIi4uLy4uL3dpZGdldC9ub2RlX21vZHVsZXMvZDMtdHJhbnNpdGlvbi9zcmMvc2VsZWN0aW9uL3RyYW5zaXRpb24uanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL2QzLXRyYW5zaXRpb24vc3JjL3NlbGVjdGlvbi9pbmRleC5qcyIsIi4uLy4uL3dpZGdldC9ub2RlX21vZHVsZXMvZDMtem9vbS9zcmMvY29uc3RhbnQuanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL2QzLXpvb20vc3JjL2V2ZW50LmpzIiwiLi4vLi4vd2lkZ2V0L25vZGVfbW9kdWxlcy9kMy16b29tL3NyYy90cmFuc2Zvcm0uanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL2QzLXpvb20vc3JjL25vZXZlbnQuanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL2QzLXpvb20vc3JjL3pvb20uanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL2RlcXVhbC9saXRlL2luZGV4Lm1qcyIsIi4uLy4uL3dpZGdldC9ub2RlX21vZHVsZXMvY2xvbmUvY2xvbmUuanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL3V1aWQvZGlzdC9lc20tYnJvd3Nlci9ybmcuanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL3V1aWQvZGlzdC9lc20tYnJvd3Nlci9yZWdleC5qcyIsIi4uLy4uL3dpZGdldC9ub2RlX21vZHVsZXMvdXVpZC9kaXN0L2VzbS1icm93c2VyL3ZhbGlkYXRlLmpzIiwiLi4vLi4vd2lkZ2V0L25vZGVfbW9kdWxlcy91dWlkL2Rpc3QvZXNtLWJyb3dzZXIvc3RyaW5naWZ5LmpzIiwiLi4vLi4vd2lkZ2V0L25vZGVfbW9kdWxlcy91dWlkL2Rpc3QvZXNtLWJyb3dzZXIvdjQuanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL3Byb3AtdHlwZXMvbm9kZV9tb2R1bGVzL3JlYWN0LWlzL2Nqcy9yZWFjdC1pcy5kZXZlbG9wbWVudC5qcyIsIi4uLy4uL3dpZGdldC9ub2RlX21vZHVsZXMvcHJvcC10eXBlcy9ub2RlX21vZHVsZXMvcmVhY3QtaXMvaW5kZXguanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL29iamVjdC1hc3NpZ24vaW5kZXguanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL3Byb3AtdHlwZXMvbGliL1JlYWN0UHJvcFR5cGVzU2VjcmV0LmpzIiwiLi4vLi4vd2lkZ2V0L25vZGVfbW9kdWxlcy9wcm9wLXR5cGVzL2xpYi9oYXMuanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL3Byb3AtdHlwZXMvY2hlY2tQcm9wVHlwZXMuanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL3Byb3AtdHlwZXMvZmFjdG9yeVdpdGhUeXBlQ2hlY2tlcnMuanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL3Byb3AtdHlwZXMvaW5kZXguanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL2NoYWluLWZ1bmN0aW9uL2luZGV4LmpzIiwiLi4vLi4vd2lkZ2V0L25vZGVfbW9kdWxlcy93YXJuaW5nL2Jyb3dzZXIuanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL3JlYWN0LWxpZmVjeWNsZXMtY29tcGF0L3JlYWN0LWxpZmVjeWNsZXMtY29tcGF0LmVzLmpzIiwiLi4vLi4vd2lkZ2V0L25vZGVfbW9kdWxlcy9AYmtyZW0vcmVhY3QtdHJhbnNpdGlvbi1ncm91cC91dGlscy9DaGlsZE1hcHBpbmcuanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL0Bia3JlbS9yZWFjdC10cmFuc2l0aW9uLWdyb3VwL1RyYW5zaXRpb25Hcm91cC5qcyIsIi4uLy4uL3dpZGdldC9ub2RlX21vZHVsZXMvQGJhYmVsL3J1bnRpbWUvaGVscGVycy9pbnRlcm9wUmVxdWlyZURlZmF1bHQuanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL0Bia3JlbS9yZWFjdC10cmFuc2l0aW9uLWdyb3VwL25vZGVfbW9kdWxlcy9kb20taGVscGVycy9jbGFzcy9oYXNDbGFzcy5qcyIsIi4uLy4uL3dpZGdldC9ub2RlX21vZHVsZXMvQGJrcmVtL3JlYWN0LXRyYW5zaXRpb24tZ3JvdXAvbm9kZV9tb2R1bGVzL2RvbS1oZWxwZXJzL2NsYXNzL2FkZENsYXNzLmpzIiwiLi4vLi4vd2lkZ2V0L25vZGVfbW9kdWxlcy9AYmtyZW0vcmVhY3QtdHJhbnNpdGlvbi1ncm91cC9ub2RlX21vZHVsZXMvZG9tLWhlbHBlcnMvY2xhc3MvcmVtb3ZlQ2xhc3MuanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL0Bia3JlbS9yZWFjdC10cmFuc2l0aW9uLWdyb3VwL25vZGVfbW9kdWxlcy9kb20taGVscGVycy91dGlsL2luRE9NLmpzIiwiLi4vLi4vd2lkZ2V0L25vZGVfbW9kdWxlcy9AYmtyZW0vcmVhY3QtdHJhbnNpdGlvbi1ncm91cC9ub2RlX21vZHVsZXMvZG9tLWhlbHBlcnMvdXRpbC9yZXF1ZXN0QW5pbWF0aW9uRnJhbWUuanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL0Bia3JlbS9yZWFjdC10cmFuc2l0aW9uLWdyb3VwL25vZGVfbW9kdWxlcy9kb20taGVscGVycy90cmFuc2l0aW9uL3Byb3BlcnRpZXMuanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL0Bia3JlbS9yZWFjdC10cmFuc2l0aW9uLWdyb3VwL3V0aWxzL1Byb3BUeXBlcy5qcyIsIi4uLy4uL3dpZGdldC9ub2RlX21vZHVsZXMvQGJrcmVtL3JlYWN0LXRyYW5zaXRpb24tZ3JvdXAvQ1NTVHJhbnNpdGlvbkdyb3VwQ2hpbGQuanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL0Bia3JlbS9yZWFjdC10cmFuc2l0aW9uLWdyb3VwL0NTU1RyYW5zaXRpb25Hcm91cC5qcyIsIi4uLy4uL3dpZGdldC9ub2RlX21vZHVsZXMvQGJrcmVtL3JlYWN0LXRyYW5zaXRpb24tZ3JvdXAvaW5kZXguanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL3JlYWN0LWQzLXRyZWUvbGliL2VzbS9UcmVlL1RyYW5zaXRpb25Hcm91cFdyYXBwZXIuanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL3JlYWN0LWQzLXRyZWUvbGliL2VzbS9Ob2RlL0RlZmF1bHROb2RlRWxlbWVudC5qcyIsIi4uLy4uL3dpZGdldC9ub2RlX21vZHVsZXMvcmVhY3QtZDMtdHJlZS9saWIvZXNtL05vZGUvaW5kZXguanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL2QzLXBhdGgvc3JjL3BhdGguanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL2QzLXNoYXBlL3NyYy9jb25zdGFudC5qcyIsIi4uLy4uL3dpZGdldC9ub2RlX21vZHVsZXMvZDMtc2hhcGUvc3JjL3BvaW50LmpzIiwiLi4vLi4vd2lkZ2V0L25vZGVfbW9kdWxlcy9kMy1zaGFwZS9zcmMvYXJyYXkuanMiLCIuLi8uLi93aWRnZXQvbm9kZV9tb2R1bGVzL2QzLXNoYXBlL3NyYy9saW5rL2luZGV4LmpzIiwiLi4vLi4vd2lkZ2V0L25vZGVfbW9kdWxlcy9yZWFjdC1kMy10cmVlL2xpYi9lc20vTGluay9pbmRleC5qcyIsIi4uLy4uL3dpZGdldC9ub2RlX21vZHVsZXMvcmVhY3QtZDMtdHJlZS9saWIvZXNtL2dsb2JhbENzcy5qcyIsIi4uLy4uL3dpZGdldC9ub2RlX21vZHVsZXMvcmVhY3QtZDMtdHJlZS9saWIvZXNtL1RyZWUvaW5kZXguanMiLCIuLi8uLi93aWRnZXQvc3JjL2ludGVyYWN0aXZlVHJlZURpc3BsYXkudHN4Il0sInNvdXJjZXNDb250ZW50IjpbIi8qKioqKioqKioqKioqKioqKioqKioqKioqKioqKioqKioqKioqKioqKioqKioqKioqKioqKioqKioqKioqKioqKioqKioqKioqKioqKipcclxuQ29weXJpZ2h0IChjKSBNaWNyb3NvZnQgQ29ycG9yYXRpb24uXHJcblxyXG5QZXJtaXNzaW9uIHRvIHVzZSwgY29weSwgbW9kaWZ5LCBhbmQvb3IgZGlzdHJpYnV0ZSB0aGlzIHNvZnR3YXJlIGZvciBhbnlcclxucHVycG9zZSB3aXRoIG9yIHdpdGhvdXQgZmVlIGlzIGhlcmVieSBncmFudGVkLlxyXG5cclxuVEhFIFNPRlRXQVJFIElTIFBST1ZJREVEIFwiQVMgSVNcIiBBTkQgVEhFIEFVVEhPUiBESVNDTEFJTVMgQUxMIFdBUlJBTlRJRVMgV0lUSFxyXG5SRUdBUkQgVE8gVEhJUyBTT0ZUV0FSRSBJTkNMVURJTkcgQUxMIElNUExJRUQgV0FSUkFOVElFUyBPRiBNRVJDSEFOVEFCSUxJVFlcclxuQU5EIEZJVE5FU1MuIElOIE5PIEVWRU5UIFNIQUxMIFRIRSBBVVRIT1IgQkUgTElBQkxFIEZPUiBBTlkgU1BFQ0lBTCwgRElSRUNULFxyXG5JTkRJUkVDVCwgT1IgQ09OU0VRVUVOVElBTCBEQU1BR0VTIE9SIEFOWSBEQU1BR0VTIFdIQVRTT0VWRVIgUkVTVUxUSU5HIEZST01cclxuTE9TUyBPRiBVU0UsIERBVEEgT1IgUFJPRklUUywgV0hFVEhFUiBJTiBBTiBBQ1RJT04gT0YgQ09OVFJBQ1QsIE5FR0xJR0VOQ0UgT1JcclxuT1RIRVIgVE9SVElPVVMgQUNUSU9OLCBBUklTSU5HIE9VVCBPRiBPUiBJTiBDT05ORUNUSU9OIFdJVEggVEhFIFVTRSBPUlxyXG5QRVJGT1JNQU5DRSBPRiBUSElTIFNPRlRXQVJFLlxyXG4qKioqKioqKioqKioqKioqKioqKioqKioqKioqKioqKioqKioqKioqKioqKioqKioqKioqKioqKioqKioqKioqKioqKioqKioqKioqKiAqL1xyXG4vKiBnbG9iYWwgUmVmbGVjdCwgUHJvbWlzZSwgU3VwcHJlc3NlZEVycm9yLCBTeW1ib2wgKi9cclxuXHJcbnZhciBleHRlbmRTdGF0aWNzID0gZnVuY3Rpb24oZCwgYikge1xyXG4gICAgZXh0ZW5kU3RhdGljcyA9IE9iamVjdC5zZXRQcm90b3R5cGVPZiB8fFxyXG4gICAgICAgICh7IF9fcHJvdG9fXzogW10gfSBpbnN0YW5jZW9mIEFycmF5ICYmIGZ1bmN0aW9uIChkLCBiKSB7IGQuX19wcm90b19fID0gYjsgfSkgfHxcclxuICAgICAgICBmdW5jdGlvbiAoZCwgYikgeyBmb3IgKHZhciBwIGluIGIpIGlmIChPYmplY3QucHJvdG90eXBlLmhhc093blByb3BlcnR5LmNhbGwoYiwgcCkpIGRbcF0gPSBiW3BdOyB9O1xyXG4gICAgcmV0dXJuIGV4dGVuZFN0YXRpY3MoZCwgYik7XHJcbn07XHJcblxyXG5leHBvcnQgZnVuY3Rpb24gX19leHRlbmRzKGQsIGIpIHtcclxuICAgIGlmICh0eXBlb2YgYiAhPT0gXCJmdW5jdGlvblwiICYmIGIgIT09IG51bGwpXHJcbiAgICAgICAgdGhyb3cgbmV3IFR5cGVFcnJvcihcIkNsYXNzIGV4dGVuZHMgdmFsdWUgXCIgKyBTdHJpbmcoYikgKyBcIiBpcyBub3QgYSBjb25zdHJ1Y3RvciBvciBudWxsXCIpO1xyXG4gICAgZXh0ZW5kU3RhdGljcyhkLCBiKTtcclxuICAgIGZ1bmN0aW9uIF9fKCkgeyB0aGlzLmNvbnN0cnVjdG9yID0gZDsgfVxyXG4gICAgZC5wcm90b3R5cGUgPSBiID09PSBudWxsID8gT2JqZWN0LmNyZWF0ZShiKSA6IChfXy5wcm90b3R5cGUgPSBiLnByb3RvdHlwZSwgbmV3IF9fKCkpO1xyXG59XHJcblxyXG5leHBvcnQgdmFyIF9fYXNzaWduID0gZnVuY3Rpb24oKSB7XHJcbiAgICBfX2Fzc2lnbiA9IE9iamVjdC5hc3NpZ24gfHwgZnVuY3Rpb24gX19hc3NpZ24odCkge1xyXG4gICAgICAgIGZvciAodmFyIHMsIGkgPSAxLCBuID0gYXJndW1lbnRzLmxlbmd0aDsgaSA8IG47IGkrKykge1xyXG4gICAgICAgICAgICBzID0gYXJndW1lbnRzW2ldO1xyXG4gICAgICAgICAgICBmb3IgKHZhciBwIGluIHMpIGlmIChPYmplY3QucHJvdG90eXBlLmhhc093blByb3BlcnR5LmNhbGwocywgcCkpIHRbcF0gPSBzW3BdO1xyXG4gICAgICAgIH1cclxuICAgICAgICByZXR1cm4gdDtcclxuICAgIH1cclxuICAgIHJldHVybiBfX2Fzc2lnbi5hcHBseSh0aGlzLCBhcmd1bWVudHMpO1xyXG59XHJcblxyXG5leHBvcnQgZnVuY3Rpb24gX19yZXN0KHMsIGUpIHtcclxuICAgIHZhciB0ID0ge307XHJcbiAgICBmb3IgKHZhciBwIGluIHMpIGlmIChPYmplY3QucHJvdG90eXBlLmhhc093blByb3BlcnR5LmNhbGwocywgcCkgJiYgZS5pbmRleE9mKHApIDwgMClcclxuICAgICAgICB0W3BdID0gc1twXTtcclxuICAgIGlmIChzICE9IG51bGwgJiYgdHlwZW9mIE9iamVjdC5nZXRPd25Qcm9wZXJ0eVN5bWJvbHMgPT09IFwiZnVuY3Rpb25cIilcclxuICAgICAgICBmb3IgKHZhciBpID0gMCwgcCA9IE9iamVjdC5nZXRPd25Qcm9wZXJ0eVN5bWJvbHMocyk7IGkgPCBwLmxlbmd0aDsgaSsrKSB7XHJcbiAgICAgICAgICAgIGlmIChlLmluZGV4T2YocFtpXSkgPCAwICYmIE9iamVjdC5wcm90b3R5cGUucHJvcGVydHlJc0VudW1lcmFibGUuY2FsbChzLCBwW2ldKSlcclxuICAgICAgICAgICAgICAgIHRbcFtpXV0gPSBzW3BbaV1dO1xyXG4gICAgICAgIH1cclxuICAgIHJldHVybiB0O1xyXG59XHJcblxyXG5leHBvcnQgZnVuY3Rpb24gX19kZWNvcmF0ZShkZWNvcmF0b3JzLCB0YXJnZXQsIGtleSwgZGVzYykge1xyXG4gICAgdmFyIGMgPSBhcmd1bWVudHMubGVuZ3RoLCByID0gYyA8IDMgPyB0YXJnZXQgOiBkZXNjID09PSBudWxsID8gZGVzYyA9IE9iamVjdC5nZXRPd25Qcm9wZXJ0eURlc2NyaXB0b3IodGFyZ2V0LCBrZXkpIDogZGVzYywgZDtcclxuICAgIGlmICh0eXBlb2YgUmVmbGVjdCA9PT0gXCJvYmplY3RcIiAmJiB0eXBlb2YgUmVmbGVjdC5kZWNvcmF0ZSA9PT0gXCJmdW5jdGlvblwiKSByID0gUmVmbGVjdC5kZWNvcmF0ZShkZWNvcmF0b3JzLCB0YXJnZXQsIGtleSwgZGVzYyk7XHJcbiAgICBlbHNlIGZvciAodmFyIGkgPSBkZWNvcmF0b3JzLmxlbmd0aCAtIDE7IGkgPj0gMDsgaS0tKSBpZiAoZCA9IGRlY29yYXRvcnNbaV0pIHIgPSAoYyA8IDMgPyBkKHIpIDogYyA+IDMgPyBkKHRhcmdldCwga2V5LCByKSA6IGQodGFyZ2V0LCBrZXkpKSB8fCByO1xyXG4gICAgcmV0dXJuIGMgPiAzICYmIHIgJiYgT2JqZWN0LmRlZmluZVByb3BlcnR5KHRhcmdldCwga2V5LCByKSwgcjtcclxufVxyXG5cclxuZXhwb3J0IGZ1bmN0aW9uIF9fcGFyYW0ocGFyYW1JbmRleCwgZGVjb3JhdG9yKSB7XHJcbiAgICByZXR1cm4gZnVuY3Rpb24gKHRhcmdldCwga2V5KSB7IGRlY29yYXRvcih0YXJnZXQsIGtleSwgcGFyYW1JbmRleCk7IH1cclxufVxyXG5cclxuZXhwb3J0IGZ1bmN0aW9uIF9fZXNEZWNvcmF0ZShjdG9yLCBkZXNjcmlwdG9ySW4sIGRlY29yYXRvcnMsIGNvbnRleHRJbiwgaW5pdGlhbGl6ZXJzLCBleHRyYUluaXRpYWxpemVycykge1xyXG4gICAgZnVuY3Rpb24gYWNjZXB0KGYpIHsgaWYgKGYgIT09IHZvaWQgMCAmJiB0eXBlb2YgZiAhPT0gXCJmdW5jdGlvblwiKSB0aHJvdyBuZXcgVHlwZUVycm9yKFwiRnVuY3Rpb24gZXhwZWN0ZWRcIik7IHJldHVybiBmOyB9XHJcbiAgICB2YXIga2luZCA9IGNvbnRleHRJbi5raW5kLCBrZXkgPSBraW5kID09PSBcImdldHRlclwiID8gXCJnZXRcIiA6IGtpbmQgPT09IFwic2V0dGVyXCIgPyBcInNldFwiIDogXCJ2YWx1ZVwiO1xyXG4gICAgdmFyIHRhcmdldCA9ICFkZXNjcmlwdG9ySW4gJiYgY3RvciA/IGNvbnRleHRJbltcInN0YXRpY1wiXSA/IGN0b3IgOiBjdG9yLnByb3RvdHlwZSA6IG51bGw7XHJcbiAgICB2YXIgZGVzY3JpcHRvciA9IGRlc2NyaXB0b3JJbiB8fCAodGFyZ2V0ID8gT2JqZWN0LmdldE93blByb3BlcnR5RGVzY3JpcHRvcih0YXJnZXQsIGNvbnRleHRJbi5uYW1lKSA6IHt9KTtcclxuICAgIHZhciBfLCBkb25lID0gZmFsc2U7XHJcbiAgICBmb3IgKHZhciBpID0gZGVjb3JhdG9ycy5sZW5ndGggLSAxOyBpID49IDA7IGktLSkge1xyXG4gICAgICAgIHZhciBjb250ZXh0ID0ge307XHJcbiAgICAgICAgZm9yICh2YXIgcCBpbiBjb250ZXh0SW4pIGNvbnRleHRbcF0gPSBwID09PSBcImFjY2Vzc1wiID8ge30gOiBjb250ZXh0SW5bcF07XHJcbiAgICAgICAgZm9yICh2YXIgcCBpbiBjb250ZXh0SW4uYWNjZXNzKSBjb250ZXh0LmFjY2Vzc1twXSA9IGNvbnRleHRJbi5hY2Nlc3NbcF07XHJcbiAgICAgICAgY29udGV4dC5hZGRJbml0aWFsaXplciA9IGZ1bmN0aW9uIChmKSB7IGlmIChkb25lKSB0aHJvdyBuZXcgVHlwZUVycm9yKFwiQ2Fubm90IGFkZCBpbml0aWFsaXplcnMgYWZ0ZXIgZGVjb3JhdGlvbiBoYXMgY29tcGxldGVkXCIpOyBleHRyYUluaXRpYWxpemVycy5wdXNoKGFjY2VwdChmIHx8IG51bGwpKTsgfTtcclxuICAgICAgICB2YXIgcmVzdWx0ID0gKDAsIGRlY29yYXRvcnNbaV0pKGtpbmQgPT09IFwiYWNjZXNzb3JcIiA/IHsgZ2V0OiBkZXNjcmlwdG9yLmdldCwgc2V0OiBkZXNjcmlwdG9yLnNldCB9IDogZGVzY3JpcHRvcltrZXldLCBjb250ZXh0KTtcclxuICAgICAgICBpZiAoa2luZCA9PT0gXCJhY2Nlc3NvclwiKSB7XHJcbiAgICAgICAgICAgIGlmIChyZXN1bHQgPT09IHZvaWQgMCkgY29udGludWU7XHJcbiAgICAgICAgICAgIGlmIChyZXN1bHQgPT09IG51bGwgfHwgdHlwZW9mIHJlc3VsdCAhPT0gXCJvYmplY3RcIikgdGhyb3cgbmV3IFR5cGVFcnJvcihcIk9iamVjdCBleHBlY3RlZFwiKTtcclxuICAgICAgICAgICAgaWYgKF8gPSBhY2NlcHQocmVzdWx0LmdldCkpIGRlc2NyaXB0b3IuZ2V0ID0gXztcclxuICAgICAgICAgICAgaWYgKF8gPSBhY2NlcHQocmVzdWx0LnNldCkpIGRlc2NyaXB0b3Iuc2V0ID0gXztcclxuICAgICAgICAgICAgaWYgKF8gPSBhY2NlcHQocmVzdWx0LmluaXQpKSBpbml0aWFsaXplcnMudW5zaGlmdChfKTtcclxuICAgICAgICB9XHJcbiAgICAgICAgZWxzZSBpZiAoXyA9IGFjY2VwdChyZXN1bHQpKSB7XHJcbiAgICAgICAgICAgIGlmIChraW5kID09PSBcImZpZWxkXCIpIGluaXRpYWxpemVycy51bnNoaWZ0KF8pO1xyXG4gICAgICAgICAgICBlbHNlIGRlc2NyaXB0b3Jba2V5XSA9IF87XHJcbiAgICAgICAgfVxyXG4gICAgfVxyXG4gICAgaWYgKHRhcmdldCkgT2JqZWN0LmRlZmluZVByb3BlcnR5KHRhcmdldCwgY29udGV4dEluLm5hbWUsIGRlc2NyaXB0b3IpO1xyXG4gICAgZG9uZSA9IHRydWU7XHJcbn07XHJcblxyXG5leHBvcnQgZnVuY3Rpb24gX19ydW5Jbml0aWFsaXplcnModGhpc0FyZywgaW5pdGlhbGl6ZXJzLCB2YWx1ZSkge1xyXG4gICAgdmFyIHVzZVZhbHVlID0gYXJndW1lbnRzLmxlbmd0aCA+IDI7XHJcbiAgICBmb3IgKHZhciBpID0gMDsgaSA8IGluaXRpYWxpemVycy5sZW5ndGg7IGkrKykge1xyXG4gICAgICAgIHZhbHVlID0gdXNlVmFsdWUgPyBpbml0aWFsaXplcnNbaV0uY2FsbCh0aGlzQXJnLCB2YWx1ZSkgOiBpbml0aWFsaXplcnNbaV0uY2FsbCh0aGlzQXJnKTtcclxuICAgIH1cclxuICAgIHJldHVybiB1c2VWYWx1ZSA/IHZhbHVlIDogdm9pZCAwO1xyXG59O1xyXG5cclxuZXhwb3J0IGZ1bmN0aW9uIF9fcHJvcEtleSh4KSB7XHJcbiAgICByZXR1cm4gdHlwZW9mIHggPT09IFwic3ltYm9sXCIgPyB4IDogXCJcIi5jb25jYXQoeCk7XHJcbn07XHJcblxyXG5leHBvcnQgZnVuY3Rpb24gX19zZXRGdW5jdGlvbk5hbWUoZiwgbmFtZSwgcHJlZml4KSB7XHJcbiAgICBpZiAodHlwZW9mIG5hbWUgPT09IFwic3ltYm9sXCIpIG5hbWUgPSBuYW1lLmRlc2NyaXB0aW9uID8gXCJbXCIuY29uY2F0KG5hbWUuZGVzY3JpcHRpb24sIFwiXVwiKSA6IFwiXCI7XHJcbiAgICByZXR1cm4gT2JqZWN0LmRlZmluZVByb3BlcnR5KGYsIFwibmFtZVwiLCB7IGNvbmZpZ3VyYWJsZTogdHJ1ZSwgdmFsdWU6IHByZWZpeCA/IFwiXCIuY29uY2F0KHByZWZpeCwgXCIgXCIsIG5hbWUpIDogbmFtZSB9KTtcclxufTtcclxuXHJcbmV4cG9ydCBmdW5jdGlvbiBfX21ldGFkYXRhKG1ldGFkYXRhS2V5LCBtZXRhZGF0YVZhbHVlKSB7XHJcbiAgICBpZiAodHlwZW9mIFJlZmxlY3QgPT09IFwib2JqZWN0XCIgJiYgdHlwZW9mIFJlZmxlY3QubWV0YWRhdGEgPT09IFwiZnVuY3Rpb25cIikgcmV0dXJuIFJlZmxlY3QubWV0YWRhdGEobWV0YWRhdGFLZXksIG1ldGFkYXRhVmFsdWUpO1xyXG59XHJcblxyXG5leHBvcnQgZnVuY3Rpb24gX19hd2FpdGVyKHRoaXNBcmcsIF9hcmd1bWVudHMsIFAsIGdlbmVyYXRvcikge1xyXG4gICAgZnVuY3Rpb24gYWRvcHQodmFsdWUpIHsgcmV0dXJuIHZhbHVlIGluc3RhbmNlb2YgUCA/IHZhbHVlIDogbmV3IFAoZnVuY3Rpb24gKHJlc29sdmUpIHsgcmVzb2x2ZSh2YWx1ZSk7IH0pOyB9XHJcbiAgICByZXR1cm4gbmV3IChQIHx8IChQID0gUHJvbWlzZSkpKGZ1bmN0aW9uIChyZXNvbHZlLCByZWplY3QpIHtcclxuICAgICAgICBmdW5jdGlvbiBmdWxmaWxsZWQodmFsdWUpIHsgdHJ5IHsgc3RlcChnZW5lcmF0b3IubmV4dCh2YWx1ZSkpOyB9IGNhdGNoIChlKSB7IHJlamVjdChlKTsgfSB9XHJcbiAgICAgICAgZnVuY3Rpb24gcmVqZWN0ZWQodmFsdWUpIHsgdHJ5IHsgc3RlcChnZW5lcmF0b3JbXCJ0aHJvd1wiXSh2YWx1ZSkpOyB9IGNhdGNoIChlKSB7IHJlamVjdChlKTsgfSB9XHJcbiAgICAgICAgZnVuY3Rpb24gc3RlcChyZXN1bHQpIHsgcmVzdWx0LmRvbmUgPyByZXNvbHZlKHJlc3VsdC52YWx1ZSkgOiBhZG9wdChyZXN1bHQudmFsdWUpLnRoZW4oZnVsZmlsbGVkLCByZWplY3RlZCk7IH1cclxuICAgICAgICBzdGVwKChnZW5lcmF0b3IgPSBnZW5lcmF0b3IuYXBwbHkodGhpc0FyZywgX2FyZ3VtZW50cyB8fCBbXSkpLm5leHQoKSk7XHJcbiAgICB9KTtcclxufVxyXG5cclxuZXhwb3J0IGZ1bmN0aW9uIF9fZ2VuZXJhdG9yKHRoaXNBcmcsIGJvZHkpIHtcclxuICAgIHZhciBfID0geyBsYWJlbDogMCwgc2VudDogZnVuY3Rpb24oKSB7IGlmICh0WzBdICYgMSkgdGhyb3cgdFsxXTsgcmV0dXJuIHRbMV07IH0sIHRyeXM6IFtdLCBvcHM6IFtdIH0sIGYsIHksIHQsIGc7XHJcbiAgICByZXR1cm4gZyA9IHsgbmV4dDogdmVyYigwKSwgXCJ0aHJvd1wiOiB2ZXJiKDEpLCBcInJldHVyblwiOiB2ZXJiKDIpIH0sIHR5cGVvZiBTeW1ib2wgPT09IFwiZnVuY3Rpb25cIiAmJiAoZ1tTeW1ib2wuaXRlcmF0b3JdID0gZnVuY3Rpb24oKSB7IHJldHVybiB0aGlzOyB9KSwgZztcclxuICAgIGZ1bmN0aW9uIHZlcmIobikgeyByZXR1cm4gZnVuY3Rpb24gKHYpIHsgcmV0dXJuIHN0ZXAoW24sIHZdKTsgfTsgfVxyXG4gICAgZnVuY3Rpb24gc3RlcChvcCkge1xyXG4gICAgICAgIGlmIChmKSB0aHJvdyBuZXcgVHlwZUVycm9yKFwiR2VuZXJhdG9yIGlzIGFscmVhZHkgZXhlY3V0aW5nLlwiKTtcclxuICAgICAgICB3aGlsZSAoZyAmJiAoZyA9IDAsIG9wWzBdICYmIChfID0gMCkpLCBfKSB0cnkge1xyXG4gICAgICAgICAgICBpZiAoZiA9IDEsIHkgJiYgKHQgPSBvcFswXSAmIDIgPyB5W1wicmV0dXJuXCJdIDogb3BbMF0gPyB5W1widGhyb3dcIl0gfHwgKCh0ID0geVtcInJldHVyblwiXSkgJiYgdC5jYWxsKHkpLCAwKSA6IHkubmV4dCkgJiYgISh0ID0gdC5jYWxsKHksIG9wWzFdKSkuZG9uZSkgcmV0dXJuIHQ7XHJcbiAgICAgICAgICAgIGlmICh5ID0gMCwgdCkgb3AgPSBbb3BbMF0gJiAyLCB0LnZhbHVlXTtcclxuICAgICAgICAgICAgc3dpdGNoIChvcFswXSkge1xyXG4gICAgICAgICAgICAgICAgY2FzZSAwOiBjYXNlIDE6IHQgPSBvcDsgYnJlYWs7XHJcbiAgICAgICAgICAgICAgICBjYXNlIDQ6IF8ubGFiZWwrKzsgcmV0dXJuIHsgdmFsdWU6IG9wWzFdLCBkb25lOiBmYWxzZSB9O1xyXG4gICAgICAgICAgICAgICAgY2FzZSA1OiBfLmxhYmVsKys7IHkgPSBvcFsxXTsgb3AgPSBbMF07IGNvbnRpbnVlO1xyXG4gICAgICAgICAgICAgICAgY2FzZSA3OiBvcCA9IF8ub3BzLnBvcCgpOyBfLnRyeXMucG9wKCk7IGNvbnRpbnVlO1xyXG4gICAgICAgICAgICAgICAgZGVmYXVsdDpcclxuICAgICAgICAgICAgICAgICAgICBpZiAoISh0ID0gXy50cnlzLCB0ID0gdC5sZW5ndGggPiAwICYmIHRbdC5sZW5ndGggLSAxXSkgJiYgKG9wWzBdID09PSA2IHx8IG9wWzBdID09PSAyKSkgeyBfID0gMDsgY29udGludWU7IH1cclxuICAgICAgICAgICAgICAgICAgICBpZiAob3BbMF0gPT09IDMgJiYgKCF0IHx8IChvcFsxXSA+IHRbMF0gJiYgb3BbMV0gPCB0WzNdKSkpIHsgXy5sYWJlbCA9IG9wWzFdOyBicmVhazsgfVxyXG4gICAgICAgICAgICAgICAgICAgIGlmIChvcFswXSA9PT0gNiAmJiBfLmxhYmVsIDwgdFsxXSkgeyBfLmxhYmVsID0gdFsxXTsgdCA9IG9wOyBicmVhazsgfVxyXG4gICAgICAgICAgICAgICAgICAgIGlmICh0ICYmIF8ubGFiZWwgPCB0WzJdKSB7IF8ubGFiZWwgPSB0WzJdOyBfLm9wcy5wdXNoKG9wKTsgYnJlYWs7IH1cclxuICAgICAgICAgICAgICAgICAgICBpZiAodFsyXSkgXy5vcHMucG9wKCk7XHJcbiAgICAgICAgICAgICAgICAgICAgXy50cnlzLnBvcCgpOyBjb250aW51ZTtcclxuICAgICAgICAgICAgfVxyXG4gICAgICAgICAgICBvcCA9IGJvZHkuY2FsbCh0aGlzQXJnLCBfKTtcclxuICAgICAgICB9IGNhdGNoIChlKSB7IG9wID0gWzYsIGVdOyB5ID0gMDsgfSBmaW5hbGx5IHsgZiA9IHQgPSAwOyB9XHJcbiAgICAgICAgaWYgKG9wWzBdICYgNSkgdGhyb3cgb3BbMV07IHJldHVybiB7IHZhbHVlOiBvcFswXSA/IG9wWzFdIDogdm9pZCAwLCBkb25lOiB0cnVlIH07XHJcbiAgICB9XHJcbn1cclxuXHJcbmV4cG9ydCB2YXIgX19jcmVhdGVCaW5kaW5nID0gT2JqZWN0LmNyZWF0ZSA/IChmdW5jdGlvbihvLCBtLCBrLCBrMikge1xyXG4gICAgaWYgKGsyID09PSB1bmRlZmluZWQpIGsyID0gaztcclxuICAgIHZhciBkZXNjID0gT2JqZWN0LmdldE93blByb3BlcnR5RGVzY3JpcHRvcihtLCBrKTtcclxuICAgIGlmICghZGVzYyB8fCAoXCJnZXRcIiBpbiBkZXNjID8gIW0uX19lc01vZHVsZSA6IGRlc2Mud3JpdGFibGUgfHwgZGVzYy5jb25maWd1cmFibGUpKSB7XHJcbiAgICAgICAgZGVzYyA9IHsgZW51bWVyYWJsZTogdHJ1ZSwgZ2V0OiBmdW5jdGlvbigpIHsgcmV0dXJuIG1ba107IH0gfTtcclxuICAgIH1cclxuICAgIE9iamVjdC5kZWZpbmVQcm9wZXJ0eShvLCBrMiwgZGVzYyk7XHJcbn0pIDogKGZ1bmN0aW9uKG8sIG0sIGssIGsyKSB7XHJcbiAgICBpZiAoazIgPT09IHVuZGVmaW5lZCkgazIgPSBrO1xyXG4gICAgb1trMl0gPSBtW2tdO1xyXG59KTtcclxuXHJcbmV4cG9ydCBmdW5jdGlvbiBfX2V4cG9ydFN0YXIobSwgbykge1xyXG4gICAgZm9yICh2YXIgcCBpbiBtKSBpZiAocCAhPT0gXCJkZWZhdWx0XCIgJiYgIU9iamVjdC5wcm90b3R5cGUuaGFzT3duUHJvcGVydHkuY2FsbChvLCBwKSkgX19jcmVhdGVCaW5kaW5nKG8sIG0sIHApO1xyXG59XHJcblxyXG5leHBvcnQgZnVuY3Rpb24gX192YWx1ZXMobykge1xyXG4gICAgdmFyIHMgPSB0eXBlb2YgU3ltYm9sID09PSBcImZ1bmN0aW9uXCIgJiYgU3ltYm9sLml0ZXJhdG9yLCBtID0gcyAmJiBvW3NdLCBpID0gMDtcclxuICAgIGlmIChtKSByZXR1cm4gbS5jYWxsKG8pO1xyXG4gICAgaWYgKG8gJiYgdHlwZW9mIG8ubGVuZ3RoID09PSBcIm51bWJlclwiKSByZXR1cm4ge1xyXG4gICAgICAgIG5leHQ6IGZ1bmN0aW9uICgpIHtcclxuICAgICAgICAgICAgaWYgKG8gJiYgaSA+PSBvLmxlbmd0aCkgbyA9IHZvaWQgMDtcclxuICAgICAgICAgICAgcmV0dXJuIHsgdmFsdWU6IG8gJiYgb1tpKytdLCBkb25lOiAhbyB9O1xyXG4gICAgICAgIH1cclxuICAgIH07XHJcbiAgICB0aHJvdyBuZXcgVHlwZUVycm9yKHMgPyBcIk9iamVjdCBpcyBub3QgaXRlcmFibGUuXCIgOiBcIlN5bWJvbC5pdGVyYXRvciBpcyBub3QgZGVmaW5lZC5cIik7XHJcbn1cclxuXHJcbmV4cG9ydCBmdW5jdGlvbiBfX3JlYWQobywgbikge1xyXG4gICAgdmFyIG0gPSB0eXBlb2YgU3ltYm9sID09PSBcImZ1bmN0aW9uXCIgJiYgb1tTeW1ib2wuaXRlcmF0b3JdO1xyXG4gICAgaWYgKCFtKSByZXR1cm4gbztcclxuICAgIHZhciBpID0gbS5jYWxsKG8pLCByLCBhciA9IFtdLCBlO1xyXG4gICAgdHJ5IHtcclxuICAgICAgICB3aGlsZSAoKG4gPT09IHZvaWQgMCB8fCBuLS0gPiAwKSAmJiAhKHIgPSBpLm5leHQoKSkuZG9uZSkgYXIucHVzaChyLnZhbHVlKTtcclxuICAgIH1cclxuICAgIGNhdGNoIChlcnJvcikgeyBlID0geyBlcnJvcjogZXJyb3IgfTsgfVxyXG4gICAgZmluYWxseSB7XHJcbiAgICAgICAgdHJ5IHtcclxuICAgICAgICAgICAgaWYgKHIgJiYgIXIuZG9uZSAmJiAobSA9IGlbXCJyZXR1cm5cIl0pKSBtLmNhbGwoaSk7XHJcbiAgICAgICAgfVxyXG4gICAgICAgIGZpbmFsbHkgeyBpZiAoZSkgdGhyb3cgZS5lcnJvcjsgfVxyXG4gICAgfVxyXG4gICAgcmV0dXJuIGFyO1xyXG59XHJcblxyXG4vKiogQGRlcHJlY2F0ZWQgKi9cclxuZXhwb3J0IGZ1bmN0aW9uIF9fc3ByZWFkKCkge1xyXG4gICAgZm9yICh2YXIgYXIgPSBbXSwgaSA9IDA7IGkgPCBhcmd1bWVudHMubGVuZ3RoOyBpKyspXHJcbiAgICAgICAgYXIgPSBhci5jb25jYXQoX19yZWFkKGFyZ3VtZW50c1tpXSkpO1xyXG4gICAgcmV0dXJuIGFyO1xyXG59XHJcblxyXG4vKiogQGRlcHJlY2F0ZWQgKi9cclxuZXhwb3J0IGZ1bmN0aW9uIF9fc3ByZWFkQXJyYXlzKCkge1xyXG4gICAgZm9yICh2YXIgcyA9IDAsIGkgPSAwLCBpbCA9IGFyZ3VtZW50cy5sZW5ndGg7IGkgPCBpbDsgaSsrKSBzICs9IGFyZ3VtZW50c1tpXS5sZW5ndGg7XHJcbiAgICBmb3IgKHZhciByID0gQXJyYXkocyksIGsgPSAwLCBpID0gMDsgaSA8IGlsOyBpKyspXHJcbiAgICAgICAgZm9yICh2YXIgYSA9IGFyZ3VtZW50c1tpXSwgaiA9IDAsIGpsID0gYS5sZW5ndGg7IGogPCBqbDsgaisrLCBrKyspXHJcbiAgICAgICAgICAgIHJba10gPSBhW2pdO1xyXG4gICAgcmV0dXJuIHI7XHJcbn1cclxuXHJcbmV4cG9ydCBmdW5jdGlvbiBfX3NwcmVhZEFycmF5KHRvLCBmcm9tLCBwYWNrKSB7XHJcbiAgICBpZiAocGFjayB8fCBhcmd1bWVudHMubGVuZ3RoID09PSAyKSBmb3IgKHZhciBpID0gMCwgbCA9IGZyb20ubGVuZ3RoLCBhcjsgaSA8IGw7IGkrKykge1xyXG4gICAgICAgIGlmIChhciB8fCAhKGkgaW4gZnJvbSkpIHtcclxuICAgICAgICAgICAgaWYgKCFhcikgYXIgPSBBcnJheS5wcm90b3R5cGUuc2xpY2UuY2FsbChmcm9tLCAwLCBpKTtcclxuICAgICAgICAgICAgYXJbaV0gPSBmcm9tW2ldO1xyXG4gICAgICAgIH1cclxuICAgIH1cclxuICAgIHJldHVybiB0by5jb25jYXQoYXIgfHwgQXJyYXkucHJvdG90eXBlLnNsaWNlLmNhbGwoZnJvbSkpO1xyXG59XHJcblxyXG5leHBvcnQgZnVuY3Rpb24gX19hd2FpdCh2KSB7XHJcbiAgICByZXR1cm4gdGhpcyBpbnN0YW5jZW9mIF9fYXdhaXQgPyAodGhpcy52ID0gdiwgdGhpcykgOiBuZXcgX19hd2FpdCh2KTtcclxufVxyXG5cclxuZXhwb3J0IGZ1bmN0aW9uIF9fYXN5bmNHZW5lcmF0b3IodGhpc0FyZywgX2FyZ3VtZW50cywgZ2VuZXJhdG9yKSB7XHJcbiAgICBpZiAoIVN5bWJvbC5hc3luY0l0ZXJhdG9yKSB0aHJvdyBuZXcgVHlwZUVycm9yKFwiU3ltYm9sLmFzeW5jSXRlcmF0b3IgaXMgbm90IGRlZmluZWQuXCIpO1xyXG4gICAgdmFyIGcgPSBnZW5lcmF0b3IuYXBwbHkodGhpc0FyZywgX2FyZ3VtZW50cyB8fCBbXSksIGksIHEgPSBbXTtcclxuICAgIHJldHVybiBpID0ge30sIHZlcmIoXCJuZXh0XCIpLCB2ZXJiKFwidGhyb3dcIiksIHZlcmIoXCJyZXR1cm5cIiksIGlbU3ltYm9sLmFzeW5jSXRlcmF0b3JdID0gZnVuY3Rpb24gKCkgeyByZXR1cm4gdGhpczsgfSwgaTtcclxuICAgIGZ1bmN0aW9uIHZlcmIobikgeyBpZiAoZ1tuXSkgaVtuXSA9IGZ1bmN0aW9uICh2KSB7IHJldHVybiBuZXcgUHJvbWlzZShmdW5jdGlvbiAoYSwgYikgeyBxLnB1c2goW24sIHYsIGEsIGJdKSA+IDEgfHwgcmVzdW1lKG4sIHYpOyB9KTsgfTsgfVxyXG4gICAgZnVuY3Rpb24gcmVzdW1lKG4sIHYpIHsgdHJ5IHsgc3RlcChnW25dKHYpKTsgfSBjYXRjaCAoZSkgeyBzZXR0bGUocVswXVszXSwgZSk7IH0gfVxyXG4gICAgZnVuY3Rpb24gc3RlcChyKSB7IHIudmFsdWUgaW5zdGFuY2VvZiBfX2F3YWl0ID8gUHJvbWlzZS5yZXNvbHZlKHIudmFsdWUudikudGhlbihmdWxmaWxsLCByZWplY3QpIDogc2V0dGxlKHFbMF1bMl0sIHIpOyB9XHJcbiAgICBmdW5jdGlvbiBmdWxmaWxsKHZhbHVlKSB7IHJlc3VtZShcIm5leHRcIiwgdmFsdWUpOyB9XHJcbiAgICBmdW5jdGlvbiByZWplY3QodmFsdWUpIHsgcmVzdW1lKFwidGhyb3dcIiwgdmFsdWUpOyB9XHJcbiAgICBmdW5jdGlvbiBzZXR0bGUoZiwgdikgeyBpZiAoZih2KSwgcS5zaGlmdCgpLCBxLmxlbmd0aCkgcmVzdW1lKHFbMF1bMF0sIHFbMF1bMV0pOyB9XHJcbn1cclxuXHJcbmV4cG9ydCBmdW5jdGlvbiBfX2FzeW5jRGVsZWdhdG9yKG8pIHtcclxuICAgIHZhciBpLCBwO1xyXG4gICAgcmV0dXJuIGkgPSB7fSwgdmVyYihcIm5leHRcIiksIHZlcmIoXCJ0aHJvd1wiLCBmdW5jdGlvbiAoZSkgeyB0aHJvdyBlOyB9KSwgdmVyYihcInJldHVyblwiKSwgaVtTeW1ib2wuaXRlcmF0b3JdID0gZnVuY3Rpb24gKCkgeyByZXR1cm4gdGhpczsgfSwgaTtcclxuICAgIGZ1bmN0aW9uIHZlcmIobiwgZikgeyBpW25dID0gb1tuXSA/IGZ1bmN0aW9uICh2KSB7IHJldHVybiAocCA9ICFwKSA/IHsgdmFsdWU6IF9fYXdhaXQob1tuXSh2KSksIGRvbmU6IGZhbHNlIH0gOiBmID8gZih2KSA6IHY7IH0gOiBmOyB9XHJcbn1cclxuXHJcbmV4cG9ydCBmdW5jdGlvbiBfX2FzeW5jVmFsdWVzKG8pIHtcclxuICAgIGlmICghU3ltYm9sLmFzeW5jSXRlcmF0b3IpIHRocm93IG5ldyBUeXBlRXJyb3IoXCJTeW1ib2wuYXN5bmNJdGVyYXRvciBpcyBub3QgZGVmaW5lZC5cIik7XHJcbiAgICB2YXIgbSA9IG9bU3ltYm9sLmFzeW5jSXRlcmF0b3JdLCBpO1xyXG4gICAgcmV0dXJuIG0gPyBtLmNhbGwobykgOiAobyA9IHR5cGVvZiBfX3ZhbHVlcyA9PT0gXCJmdW5jdGlvblwiID8gX192YWx1ZXMobykgOiBvW1N5bWJvbC5pdGVyYXRvcl0oKSwgaSA9IHt9LCB2ZXJiKFwibmV4dFwiKSwgdmVyYihcInRocm93XCIpLCB2ZXJiKFwicmV0dXJuXCIpLCBpW1N5bWJvbC5hc3luY0l0ZXJhdG9yXSA9IGZ1bmN0aW9uICgpIHsgcmV0dXJuIHRoaXM7IH0sIGkpO1xyXG4gICAgZnVuY3Rpb24gdmVyYihuKSB7IGlbbl0gPSBvW25dICYmIGZ1bmN0aW9uICh2KSB7IHJldHVybiBuZXcgUHJvbWlzZShmdW5jdGlvbiAocmVzb2x2ZSwgcmVqZWN0KSB7IHYgPSBvW25dKHYpLCBzZXR0bGUocmVzb2x2ZSwgcmVqZWN0LCB2LmRvbmUsIHYudmFsdWUpOyB9KTsgfTsgfVxyXG4gICAgZnVuY3Rpb24gc2V0dGxlKHJlc29sdmUsIHJlamVjdCwgZCwgdikgeyBQcm9taXNlLnJlc29sdmUodikudGhlbihmdW5jdGlvbih2KSB7IHJlc29sdmUoeyB2YWx1ZTogdiwgZG9uZTogZCB9KTsgfSwgcmVqZWN0KTsgfVxyXG59XHJcblxyXG5leHBvcnQgZnVuY3Rpb24gX19tYWtlVGVtcGxhdGVPYmplY3QoY29va2VkLCByYXcpIHtcclxuICAgIGlmIChPYmplY3QuZGVmaW5lUHJvcGVydHkpIHsgT2JqZWN0LmRlZmluZVByb3BlcnR5KGNvb2tlZCwgXCJyYXdcIiwgeyB2YWx1ZTogcmF3IH0pOyB9IGVsc2UgeyBjb29rZWQucmF3ID0gcmF3OyB9XHJcbiAgICByZXR1cm4gY29va2VkO1xyXG59O1xyXG5cclxudmFyIF9fc2V0TW9kdWxlRGVmYXVsdCA9IE9iamVjdC5jcmVhdGUgPyAoZnVuY3Rpb24obywgdikge1xyXG4gICAgT2JqZWN0LmRlZmluZVByb3BlcnR5KG8sIFwiZGVmYXVsdFwiLCB7IGVudW1lcmFibGU6IHRydWUsIHZhbHVlOiB2IH0pO1xyXG59KSA6IGZ1bmN0aW9uKG8sIHYpIHtcclxuICAgIG9bXCJkZWZhdWx0XCJdID0gdjtcclxufTtcclxuXHJcbmV4cG9ydCBmdW5jdGlvbiBfX2ltcG9ydFN0YXIobW9kKSB7XHJcbiAgICBpZiAobW9kICYmIG1vZC5fX2VzTW9kdWxlKSByZXR1cm4gbW9kO1xyXG4gICAgdmFyIHJlc3VsdCA9IHt9O1xyXG4gICAgaWYgKG1vZCAhPSBudWxsKSBmb3IgKHZhciBrIGluIG1vZCkgaWYgKGsgIT09IFwiZGVmYXVsdFwiICYmIE9iamVjdC5wcm90b3R5cGUuaGFzT3duUHJvcGVydHkuY2FsbChtb2QsIGspKSBfX2NyZWF0ZUJpbmRpbmcocmVzdWx0LCBtb2QsIGspO1xyXG4gICAgX19zZXRNb2R1bGVEZWZhdWx0KHJlc3VsdCwgbW9kKTtcclxuICAgIHJldHVybiByZXN1bHQ7XHJcbn1cclxuXHJcbmV4cG9ydCBmdW5jdGlvbiBfX2ltcG9ydERlZmF1bHQobW9kKSB7XHJcbiAgICByZXR1cm4gKG1vZCAmJiBtb2QuX19lc01vZHVsZSkgPyBtb2QgOiB7IGRlZmF1bHQ6IG1vZCB9O1xyXG59XHJcblxyXG5leHBvcnQgZnVuY3Rpb24gX19jbGFzc1ByaXZhdGVGaWVsZEdldChyZWNlaXZlciwgc3RhdGUsIGtpbmQsIGYpIHtcclxuICAgIGlmIChraW5kID09PSBcImFcIiAmJiAhZikgdGhyb3cgbmV3IFR5cGVFcnJvcihcIlByaXZhdGUgYWNjZXNzb3Igd2FzIGRlZmluZWQgd2l0aG91dCBhIGdldHRlclwiKTtcclxuICAgIGlmICh0eXBlb2Ygc3RhdGUgPT09IFwiZnVuY3Rpb25cIiA/IHJlY2VpdmVyICE9PSBzdGF0ZSB8fCAhZiA6ICFzdGF0ZS5oYXMocmVjZWl2ZXIpKSB0aHJvdyBuZXcgVHlwZUVycm9yKFwiQ2Fubm90IHJlYWQgcHJpdmF0ZSBtZW1iZXIgZnJvbSBhbiBvYmplY3Qgd2hvc2UgY2xhc3MgZGlkIG5vdCBkZWNsYXJlIGl0XCIpO1xyXG4gICAgcmV0dXJuIGtpbmQgPT09IFwibVwiID8gZiA6IGtpbmQgPT09IFwiYVwiID8gZi5jYWxsKHJlY2VpdmVyKSA6IGYgPyBmLnZhbHVlIDogc3RhdGUuZ2V0KHJlY2VpdmVyKTtcclxufVxyXG5cclxuZXhwb3J0IGZ1bmN0aW9uIF9fY2xhc3NQcml2YXRlRmllbGRTZXQocmVjZWl2ZXIsIHN0YXRlLCB2YWx1ZSwga2luZCwgZikge1xyXG4gICAgaWYgKGtpbmQgPT09IFwibVwiKSB0aHJvdyBuZXcgVHlwZUVycm9yKFwiUHJpdmF0ZSBtZXRob2QgaXMgbm90IHdyaXRhYmxlXCIpO1xyXG4gICAgaWYgKGtpbmQgPT09IFwiYVwiICYmICFmKSB0aHJvdyBuZXcgVHlwZUVycm9yKFwiUHJpdmF0ZSBhY2Nlc3NvciB3YXMgZGVmaW5lZCB3aXRob3V0IGEgc2V0dGVyXCIpO1xyXG4gICAgaWYgKHR5cGVvZiBzdGF0ZSA9PT0gXCJmdW5jdGlvblwiID8gcmVjZWl2ZXIgIT09IHN0YXRlIHx8ICFmIDogIXN0YXRlLmhhcyhyZWNlaXZlcikpIHRocm93IG5ldyBUeXBlRXJyb3IoXCJDYW5ub3Qgd3JpdGUgcHJpdmF0ZSBtZW1iZXIgdG8gYW4gb2JqZWN0IHdob3NlIGNsYXNzIGRpZCBub3QgZGVjbGFyZSBpdFwiKTtcclxuICAgIHJldHVybiAoa2luZCA9PT0gXCJhXCIgPyBmLmNhbGwocmVjZWl2ZXIsIHZhbHVlKSA6IGYgPyBmLnZhbHVlID0gdmFsdWUgOiBzdGF0ZS5zZXQocmVjZWl2ZXIsIHZhbHVlKSksIHZhbHVlO1xyXG59XHJcblxyXG5leHBvcnQgZnVuY3Rpb24gX19jbGFzc1ByaXZhdGVGaWVsZEluKHN0YXRlLCByZWNlaXZlcikge1xyXG4gICAgaWYgKHJlY2VpdmVyID09PSBudWxsIHx8ICh0eXBlb2YgcmVjZWl2ZXIgIT09IFwib2JqZWN0XCIgJiYgdHlwZW9mIHJlY2VpdmVyICE9PSBcImZ1bmN0aW9uXCIpKSB0aHJvdyBuZXcgVHlwZUVycm9yKFwiQ2Fubm90IHVzZSAnaW4nIG9wZXJhdG9yIG9uIG5vbi1vYmplY3RcIik7XHJcbiAgICByZXR1cm4gdHlwZW9mIHN0YXRlID09PSBcImZ1bmN0aW9uXCIgPyByZWNlaXZlciA9PT0gc3RhdGUgOiBzdGF0ZS5oYXMocmVjZWl2ZXIpO1xyXG59XHJcblxyXG5leHBvcnQgZnVuY3Rpb24gX19hZGREaXNwb3NhYmxlUmVzb3VyY2UoZW52LCB2YWx1ZSwgYXN5bmMpIHtcclxuICAgIGlmICh2YWx1ZSAhPT0gbnVsbCAmJiB2YWx1ZSAhPT0gdm9pZCAwKSB7XHJcbiAgICAgICAgaWYgKHR5cGVvZiB2YWx1ZSAhPT0gXCJvYmplY3RcIiAmJiB0eXBlb2YgdmFsdWUgIT09IFwiZnVuY3Rpb25cIikgdGhyb3cgbmV3IFR5cGVFcnJvcihcIk9iamVjdCBleHBlY3RlZC5cIik7XHJcbiAgICAgICAgdmFyIGRpc3Bvc2U7XHJcbiAgICAgICAgaWYgKGFzeW5jKSB7XHJcbiAgICAgICAgICAgIGlmICghU3ltYm9sLmFzeW5jRGlzcG9zZSkgdGhyb3cgbmV3IFR5cGVFcnJvcihcIlN5bWJvbC5hc3luY0Rpc3Bvc2UgaXMgbm90IGRlZmluZWQuXCIpO1xyXG4gICAgICAgICAgICBkaXNwb3NlID0gdmFsdWVbU3ltYm9sLmFzeW5jRGlzcG9zZV07XHJcbiAgICAgICAgfVxyXG4gICAgICAgIGlmIChkaXNwb3NlID09PSB2b2lkIDApIHtcclxuICAgICAgICAgICAgaWYgKCFTeW1ib2wuZGlzcG9zZSkgdGhyb3cgbmV3IFR5cGVFcnJvcihcIlN5bWJvbC5kaXNwb3NlIGlzIG5vdCBkZWZpbmVkLlwiKTtcclxuICAgICAgICAgICAgZGlzcG9zZSA9IHZhbHVlW1N5bWJvbC5kaXNwb3NlXTtcclxuICAgICAgICB9XHJcbiAgICAgICAgaWYgKHR5cGVvZiBkaXNwb3NlICE9PSBcImZ1bmN0aW9uXCIpIHRocm93IG5ldyBUeXBlRXJyb3IoXCJPYmplY3Qgbm90IGRpc3Bvc2FibGUuXCIpO1xyXG4gICAgICAgIGVudi5zdGFjay5wdXNoKHsgdmFsdWU6IHZhbHVlLCBkaXNwb3NlOiBkaXNwb3NlLCBhc3luYzogYXN5bmMgfSk7XHJcbiAgICB9XHJcbiAgICBlbHNlIGlmIChhc3luYykge1xyXG4gICAgICAgIGVudi5zdGFjay5wdXNoKHsgYXN5bmM6IHRydWUgfSk7XHJcbiAgICB9XHJcbiAgICByZXR1cm4gdmFsdWU7XHJcbn1cclxuXHJcbnZhciBfU3VwcHJlc3NlZEVycm9yID0gdHlwZW9mIFN1cHByZXNzZWRFcnJvciA9PT0gXCJmdW5jdGlvblwiID8gU3VwcHJlc3NlZEVycm9yIDogZnVuY3Rpb24gKGVycm9yLCBzdXBwcmVzc2VkLCBtZXNzYWdlKSB7XHJcbiAgICB2YXIgZSA9IG5ldyBFcnJvcihtZXNzYWdlKTtcclxuICAgIHJldHVybiBlLm5hbWUgPSBcIlN1cHByZXNzZWRFcnJvclwiLCBlLmVycm9yID0gZXJyb3IsIGUuc3VwcHJlc3NlZCA9IHN1cHByZXNzZWQsIGU7XHJcbn07XHJcblxyXG5leHBvcnQgZnVuY3Rpb24gX19kaXNwb3NlUmVzb3VyY2VzKGVudikge1xyXG4gICAgZnVuY3Rpb24gZmFpbChlKSB7XHJcbiAgICAgICAgZW52LmVycm9yID0gZW52Lmhhc0Vycm9yID8gbmV3IF9TdXBwcmVzc2VkRXJyb3IoZSwgZW52LmVycm9yLCBcIkFuIGVycm9yIHdhcyBzdXBwcmVzc2VkIGR1cmluZyBkaXNwb3NhbC5cIikgOiBlO1xyXG4gICAgICAgIGVudi5oYXNFcnJvciA9IHRydWU7XHJcbiAgICB9XHJcbiAgICBmdW5jdGlvbiBuZXh0KCkge1xyXG4gICAgICAgIHdoaWxlIChlbnYuc3RhY2subGVuZ3RoKSB7XHJcbiAgICAgICAgICAgIHZhciByZWMgPSBlbnYuc3RhY2sucG9wKCk7XHJcbiAgICAgICAgICAgIHRyeSB7XHJcbiAgICAgICAgICAgICAgICB2YXIgcmVzdWx0ID0gcmVjLmRpc3Bvc2UgJiYgcmVjLmRpc3Bvc2UuY2FsbChyZWMudmFsdWUpO1xyXG4gICAgICAgICAgICAgICAgaWYgKHJlYy5hc3luYykgcmV0dXJuIFByb21pc2UucmVzb2x2ZShyZXN1bHQpLnRoZW4obmV4dCwgZnVuY3Rpb24oZSkgeyBmYWlsKGUpOyByZXR1cm4gbmV4dCgpOyB9KTtcclxuICAgICAgICAgICAgfVxyXG4gICAgICAgICAgICBjYXRjaCAoZSkge1xyXG4gICAgICAgICAgICAgICAgZmFpbChlKTtcclxuICAgICAgICAgICAgfVxyXG4gICAgICAgIH1cclxuICAgICAgICBpZiAoZW52Lmhhc0Vycm9yKSB0aHJvdyBlbnYuZXJyb3I7XHJcbiAgICB9XHJcbiAgICByZXR1cm4gbmV4dCgpO1xyXG59XHJcblxyXG5leHBvcnQgZGVmYXVsdCB7XHJcbiAgICBfX2V4dGVuZHM6IF9fZXh0ZW5kcyxcclxuICAgIF9fYXNzaWduOiBfX2Fzc2lnbixcclxuICAgIF9fcmVzdDogX19yZXN0LFxyXG4gICAgX19kZWNvcmF0ZTogX19kZWNvcmF0ZSxcclxuICAgIF9fcGFyYW06IF9fcGFyYW0sXHJcbiAgICBfX21ldGFkYXRhOiBfX21ldGFkYXRhLFxyXG4gICAgX19hd2FpdGVyOiBfX2F3YWl0ZXIsXHJcbiAgICBfX2dlbmVyYXRvcjogX19nZW5lcmF0b3IsXHJcbiAgICBfX2NyZWF0ZUJpbmRpbmc6IF9fY3JlYXRlQmluZGluZyxcclxuICAgIF9fZXhwb3J0U3RhcjogX19leHBvcnRTdGFyLFxyXG4gICAgX192YWx1ZXM6IF9fdmFsdWVzLFxyXG4gICAgX19yZWFkOiBfX3JlYWQsXHJcbiAgICBfX3NwcmVhZDogX19zcHJlYWQsXHJcbiAgICBfX3NwcmVhZEFycmF5czogX19zcHJlYWRBcnJheXMsXHJcbiAgICBfX3NwcmVhZEFycmF5OiBfX3NwcmVhZEFycmF5LFxyXG4gICAgX19hd2FpdDogX19hd2FpdCxcclxuICAgIF9fYXN5bmNHZW5lcmF0b3I6IF9fYXN5bmNHZW5lcmF0b3IsXHJcbiAgICBfX2FzeW5jRGVsZWdhdG9yOiBfX2FzeW5jRGVsZWdhdG9yLFxyXG4gICAgX19hc3luY1ZhbHVlczogX19hc3luY1ZhbHVlcyxcclxuICAgIF9fbWFrZVRlbXBsYXRlT2JqZWN0OiBfX21ha2VUZW1wbGF0ZU9iamVjdCxcclxuICAgIF9faW1wb3J0U3RhcjogX19pbXBvcnRTdGFyLFxyXG4gICAgX19pbXBvcnREZWZhdWx0OiBfX2ltcG9ydERlZmF1bHQsXHJcbiAgICBfX2NsYXNzUHJpdmF0ZUZpZWxkR2V0OiBfX2NsYXNzUHJpdmF0ZUZpZWxkR2V0LFxyXG4gICAgX19jbGFzc1ByaXZhdGVGaWVsZFNldDogX19jbGFzc1ByaXZhdGVGaWVsZFNldCxcclxuICAgIF9fY2xhc3NQcml2YXRlRmllbGRJbjogX19jbGFzc1ByaXZhdGVGaWVsZEluLFxyXG4gICAgX19hZGREaXNwb3NhYmxlUmVzb3VyY2U6IF9fYWRkRGlzcG9zYWJsZVJlc291cmNlLFxyXG4gICAgX19kaXNwb3NlUmVzb3VyY2VzOiBfX2Rpc3Bvc2VSZXNvdXJjZXMsXHJcbn07XHJcbiIsImZ1bmN0aW9uIGNvdW50KG5vZGUpIHtcbiAgdmFyIHN1bSA9IDAsXG4gICAgICBjaGlsZHJlbiA9IG5vZGUuY2hpbGRyZW4sXG4gICAgICBpID0gY2hpbGRyZW4gJiYgY2hpbGRyZW4ubGVuZ3RoO1xuICBpZiAoIWkpIHN1bSA9IDE7XG4gIGVsc2Ugd2hpbGUgKC0taSA+PSAwKSBzdW0gKz0gY2hpbGRyZW5baV0udmFsdWU7XG4gIG5vZGUudmFsdWUgPSBzdW07XG59XG5cbmV4cG9ydCBkZWZhdWx0IGZ1bmN0aW9uKCkge1xuICByZXR1cm4gdGhpcy5lYWNoQWZ0ZXIoY291bnQpO1xufVxuIiwiZXhwb3J0IGRlZmF1bHQgZnVuY3Rpb24oY2FsbGJhY2spIHtcbiAgdmFyIG5vZGUgPSB0aGlzLCBjdXJyZW50LCBuZXh0ID0gW25vZGVdLCBjaGlsZHJlbiwgaSwgbjtcbiAgZG8ge1xuICAgIGN1cnJlbnQgPSBuZXh0LnJldmVyc2UoKSwgbmV4dCA9IFtdO1xuICAgIHdoaWxlIChub2RlID0gY3VycmVudC5wb3AoKSkge1xuICAgICAgY2FsbGJhY2sobm9kZSksIGNoaWxkcmVuID0gbm9kZS5jaGlsZHJlbjtcbiAgICAgIGlmIChjaGlsZHJlbikgZm9yIChpID0gMCwgbiA9IGNoaWxkcmVuLmxlbmd0aDsgaSA8IG47ICsraSkge1xuICAgICAgICBuZXh0LnB1c2goY2hpbGRyZW5baV0pO1xuICAgICAgfVxuICAgIH1cbiAgfSB3aGlsZSAobmV4dC5sZW5ndGgpO1xuICByZXR1cm4gdGhpcztcbn1cbiIsImV4cG9ydCBkZWZhdWx0IGZ1bmN0aW9uKGNhbGxiYWNrKSB7XG4gIHZhciBub2RlID0gdGhpcywgbm9kZXMgPSBbbm9kZV0sIGNoaWxkcmVuLCBpO1xuICB3aGlsZSAobm9kZSA9IG5vZGVzLnBvcCgpKSB7XG4gICAgY2FsbGJhY2sobm9kZSksIGNoaWxkcmVuID0gbm9kZS5jaGlsZHJlbjtcbiAgICBpZiAoY2hpbGRyZW4pIGZvciAoaSA9IGNoaWxkcmVuLmxlbmd0aCAtIDE7IGkgPj0gMDsgLS1pKSB7XG4gICAgICBub2Rlcy5wdXNoKGNoaWxkcmVuW2ldKTtcbiAgICB9XG4gIH1cbiAgcmV0dXJuIHRoaXM7XG59XG4iLCJleHBvcnQgZGVmYXVsdCBmdW5jdGlvbihjYWxsYmFjaykge1xuICB2YXIgbm9kZSA9IHRoaXMsIG5vZGVzID0gW25vZGVdLCBuZXh0ID0gW10sIGNoaWxkcmVuLCBpLCBuO1xuICB3aGlsZSAobm9kZSA9IG5vZGVzLnBvcCgpKSB7XG4gICAgbmV4dC5wdXNoKG5vZGUpLCBjaGlsZHJlbiA9IG5vZGUuY2hpbGRyZW47XG4gICAgaWYgKGNoaWxkcmVuKSBmb3IgKGkgPSAwLCBuID0gY2hpbGRyZW4ubGVuZ3RoOyBpIDwgbjsgKytpKSB7XG4gICAgICBub2Rlcy5wdXNoKGNoaWxkcmVuW2ldKTtcbiAgICB9XG4gIH1cbiAgd2hpbGUgKG5vZGUgPSBuZXh0LnBvcCgpKSB7XG4gICAgY2FsbGJhY2sobm9kZSk7XG4gIH1cbiAgcmV0dXJuIHRoaXM7XG59XG4iLCJleHBvcnQgZGVmYXVsdCBmdW5jdGlvbih2YWx1ZSkge1xuICByZXR1cm4gdGhpcy5lYWNoQWZ0ZXIoZnVuY3Rpb24obm9kZSkge1xuICAgIHZhciBzdW0gPSArdmFsdWUobm9kZS5kYXRhKSB8fCAwLFxuICAgICAgICBjaGlsZHJlbiA9IG5vZGUuY2hpbGRyZW4sXG4gICAgICAgIGkgPSBjaGlsZHJlbiAmJiBjaGlsZHJlbi5sZW5ndGg7XG4gICAgd2hpbGUgKC0taSA+PSAwKSBzdW0gKz0gY2hpbGRyZW5baV0udmFsdWU7XG4gICAgbm9kZS52YWx1ZSA9IHN1bTtcbiAgfSk7XG59XG4iLCJleHBvcnQgZGVmYXVsdCBmdW5jdGlvbihjb21wYXJlKSB7XG4gIHJldHVybiB0aGlzLmVhY2hCZWZvcmUoZnVuY3Rpb24obm9kZSkge1xuICAgIGlmIChub2RlLmNoaWxkcmVuKSB7XG4gICAgICBub2RlLmNoaWxkcmVuLnNvcnQoY29tcGFyZSk7XG4gICAgfVxuICB9KTtcbn1cbiIsImV4cG9ydCBkZWZhdWx0IGZ1bmN0aW9uKGVuZCkge1xuICB2YXIgc3RhcnQgPSB0aGlzLFxuICAgICAgYW5jZXN0b3IgPSBsZWFzdENvbW1vbkFuY2VzdG9yKHN0YXJ0LCBlbmQpLFxuICAgICAgbm9kZXMgPSBbc3RhcnRdO1xuICB3aGlsZSAoc3RhcnQgIT09IGFuY2VzdG9yKSB7XG4gICAgc3RhcnQgPSBzdGFydC5wYXJlbnQ7XG4gICAgbm9kZXMucHVzaChzdGFydCk7XG4gIH1cbiAgdmFyIGsgPSBub2Rlcy5sZW5ndGg7XG4gIHdoaWxlIChlbmQgIT09IGFuY2VzdG9yKSB7XG4gICAgbm9kZXMuc3BsaWNlKGssIDAsIGVuZCk7XG4gICAgZW5kID0gZW5kLnBhcmVudDtcbiAgfVxuICByZXR1cm4gbm9kZXM7XG59XG5cbmZ1bmN0aW9uIGxlYXN0Q29tbW9uQW5jZXN0b3IoYSwgYikge1xuICBpZiAoYSA9PT0gYikgcmV0dXJuIGE7XG4gIHZhciBhTm9kZXMgPSBhLmFuY2VzdG9ycygpLFxuICAgICAgYk5vZGVzID0gYi5hbmNlc3RvcnMoKSxcbiAgICAgIGMgPSBudWxsO1xuICBhID0gYU5vZGVzLnBvcCgpO1xuICBiID0gYk5vZGVzLnBvcCgpO1xuICB3aGlsZSAoYSA9PT0gYikge1xuICAgIGMgPSBhO1xuICAgIGEgPSBhTm9kZXMucG9wKCk7XG4gICAgYiA9IGJOb2Rlcy5wb3AoKTtcbiAgfVxuICByZXR1cm4gYztcbn1cbiIsImV4cG9ydCBkZWZhdWx0IGZ1bmN0aW9uKCkge1xuICB2YXIgbm9kZSA9IHRoaXMsIG5vZGVzID0gW25vZGVdO1xuICB3aGlsZSAobm9kZSA9IG5vZGUucGFyZW50KSB7XG4gICAgbm9kZXMucHVzaChub2RlKTtcbiAgfVxuICByZXR1cm4gbm9kZXM7XG59XG4iLCJleHBvcnQgZGVmYXVsdCBmdW5jdGlvbigpIHtcbiAgdmFyIG5vZGVzID0gW107XG4gIHRoaXMuZWFjaChmdW5jdGlvbihub2RlKSB7XG4gICAgbm9kZXMucHVzaChub2RlKTtcbiAgfSk7XG4gIHJldHVybiBub2Rlcztcbn1cbiIsImV4cG9ydCBkZWZhdWx0IGZ1bmN0aW9uKCkge1xuICB2YXIgbGVhdmVzID0gW107XG4gIHRoaXMuZWFjaEJlZm9yZShmdW5jdGlvbihub2RlKSB7XG4gICAgaWYgKCFub2RlLmNoaWxkcmVuKSB7XG4gICAgICBsZWF2ZXMucHVzaChub2RlKTtcbiAgICB9XG4gIH0pO1xuICByZXR1cm4gbGVhdmVzO1xufVxuIiwiZXhwb3J0IGRlZmF1bHQgZnVuY3Rpb24oKSB7XG4gIHZhciByb290ID0gdGhpcywgbGlua3MgPSBbXTtcbiAgcm9vdC5lYWNoKGZ1bmN0aW9uKG5vZGUpIHtcbiAgICBpZiAobm9kZSAhPT0gcm9vdCkgeyAvLyBEb27igJl0IGluY2x1ZGUgdGhlIHJvb3TigJlzIHBhcmVudCwgaWYgYW55LlxuICAgICAgbGlua3MucHVzaCh7c291cmNlOiBub2RlLnBhcmVudCwgdGFyZ2V0OiBub2RlfSk7XG4gICAgfVxuICB9KTtcbiAgcmV0dXJuIGxpbmtzO1xufVxuIiwiaW1wb3J0IG5vZGVfY291bnQgZnJvbSBcIi4vY291bnQuanNcIjtcbmltcG9ydCBub2RlX2VhY2ggZnJvbSBcIi4vZWFjaC5qc1wiO1xuaW1wb3J0IG5vZGVfZWFjaEJlZm9yZSBmcm9tIFwiLi9lYWNoQmVmb3JlLmpzXCI7XG5pbXBvcnQgbm9kZV9lYWNoQWZ0ZXIgZnJvbSBcIi4vZWFjaEFmdGVyLmpzXCI7XG5pbXBvcnQgbm9kZV9zdW0gZnJvbSBcIi4vc3VtLmpzXCI7XG5pbXBvcnQgbm9kZV9zb3J0IGZyb20gXCIuL3NvcnQuanNcIjtcbmltcG9ydCBub2RlX3BhdGggZnJvbSBcIi4vcGF0aC5qc1wiO1xuaW1wb3J0IG5vZGVfYW5jZXN0b3JzIGZyb20gXCIuL2FuY2VzdG9ycy5qc1wiO1xuaW1wb3J0IG5vZGVfZGVzY2VuZGFudHMgZnJvbSBcIi4vZGVzY2VuZGFudHMuanNcIjtcbmltcG9ydCBub2RlX2xlYXZlcyBmcm9tIFwiLi9sZWF2ZXMuanNcIjtcbmltcG9ydCBub2RlX2xpbmtzIGZyb20gXCIuL2xpbmtzLmpzXCI7XG5cbmV4cG9ydCBkZWZhdWx0IGZ1bmN0aW9uIGhpZXJhcmNoeShkYXRhLCBjaGlsZHJlbikge1xuICB2YXIgcm9vdCA9IG5ldyBOb2RlKGRhdGEpLFxuICAgICAgdmFsdWVkID0gK2RhdGEudmFsdWUgJiYgKHJvb3QudmFsdWUgPSBkYXRhLnZhbHVlKSxcbiAgICAgIG5vZGUsXG4gICAgICBub2RlcyA9IFtyb290XSxcbiAgICAgIGNoaWxkLFxuICAgICAgY2hpbGRzLFxuICAgICAgaSxcbiAgICAgIG47XG5cbiAgaWYgKGNoaWxkcmVuID09IG51bGwpIGNoaWxkcmVuID0gZGVmYXVsdENoaWxkcmVuO1xuXG4gIHdoaWxlIChub2RlID0gbm9kZXMucG9wKCkpIHtcbiAgICBpZiAodmFsdWVkKSBub2RlLnZhbHVlID0gK25vZGUuZGF0YS52YWx1ZTtcbiAgICBpZiAoKGNoaWxkcyA9IGNoaWxkcmVuKG5vZGUuZGF0YSkpICYmIChuID0gY2hpbGRzLmxlbmd0aCkpIHtcbiAgICAgIG5vZGUuY2hpbGRyZW4gPSBuZXcgQXJyYXkobik7XG4gICAgICBmb3IgKGkgPSBuIC0gMTsgaSA+PSAwOyAtLWkpIHtcbiAgICAgICAgbm9kZXMucHVzaChjaGlsZCA9IG5vZGUuY2hpbGRyZW5baV0gPSBuZXcgTm9kZShjaGlsZHNbaV0pKTtcbiAgICAgICAgY2hpbGQucGFyZW50ID0gbm9kZTtcbiAgICAgICAgY2hpbGQuZGVwdGggPSBub2RlLmRlcHRoICsgMTtcbiAgICAgIH1cbiAgICB9XG4gIH1cblxuICByZXR1cm4gcm9vdC5lYWNoQmVmb3JlKGNvbXB1dGVIZWlnaHQpO1xufVxuXG5mdW5jdGlvbiBub2RlX2NvcHkoKSB7XG4gIHJldHVybiBoaWVyYXJjaHkodGhpcykuZWFjaEJlZm9yZShjb3B5RGF0YSk7XG59XG5cbmZ1bmN0aW9uIGRlZmF1bHRDaGlsZHJlbihkKSB7XG4gIHJldHVybiBkLmNoaWxkcmVuO1xufVxuXG5mdW5jdGlvbiBjb3B5RGF0YShub2RlKSB7XG4gIG5vZGUuZGF0YSA9IG5vZGUuZGF0YS5kYXRhO1xufVxuXG5leHBvcnQgZnVuY3Rpb24gY29tcHV0ZUhlaWdodChub2RlKSB7XG4gIHZhciBoZWlnaHQgPSAwO1xuICBkbyBub2RlLmhlaWdodCA9IGhlaWdodDtcbiAgd2hpbGUgKChub2RlID0gbm9kZS5wYXJlbnQpICYmIChub2RlLmhlaWdodCA8ICsraGVpZ2h0KSk7XG59XG5cbmV4cG9ydCBmdW5jdGlvbiBOb2RlKGRhdGEpIHtcbiAgdGhpcy5kYXRhID0gZGF0YTtcbiAgdGhpcy5kZXB0aCA9XG4gIHRoaXMuaGVpZ2h0ID0gMDtcbiAgdGhpcy5wYXJlbnQgPSBudWxsO1xufVxuXG5Ob2RlLnByb3RvdHlwZSA9IGhpZXJhcmNoeS5wcm90b3R5cGUgPSB7XG4gIGNvbnN0cnVjdG9yOiBOb2RlLFxuICBjb3VudDogbm9kZV9jb3VudCxcbiAgZWFjaDogbm9kZV9lYWNoLFxuICBlYWNoQWZ0ZXI6IG5vZGVfZWFjaEFmdGVyLFxuICBlYWNoQmVmb3JlOiBub2RlX2VhY2hCZWZvcmUsXG4gIHN1bTogbm9kZV9zdW0sXG4gIHNvcnQ6IG5vZGVfc29ydCxcbiAgcGF0aDogbm9kZV9wYXRoLFxuICBhbmNlc3RvcnM6IG5vZGVfYW5jZXN0b3JzLFxuICBkZXNjZW5kYW50czogbm9kZV9kZXNjZW5kYW50cyxcbiAgbGVhdmVzOiBub2RlX2xlYXZlcyxcbiAgbGlua3M6IG5vZGVfbGlua3MsXG4gIGNvcHk6IG5vZGVfY29weVxufTtcbiIsImltcG9ydCB7Tm9kZX0gZnJvbSBcIi4vaGllcmFyY2h5L2luZGV4LmpzXCI7XG5cbmZ1bmN0aW9uIGRlZmF1bHRTZXBhcmF0aW9uKGEsIGIpIHtcbiAgcmV0dXJuIGEucGFyZW50ID09PSBiLnBhcmVudCA/IDEgOiAyO1xufVxuXG4vLyBmdW5jdGlvbiByYWRpYWxTZXBhcmF0aW9uKGEsIGIpIHtcbi8vICAgcmV0dXJuIChhLnBhcmVudCA9PT0gYi5wYXJlbnQgPyAxIDogMikgLyBhLmRlcHRoO1xuLy8gfVxuXG4vLyBUaGlzIGZ1bmN0aW9uIGlzIHVzZWQgdG8gdHJhdmVyc2UgdGhlIGxlZnQgY29udG91ciBvZiBhIHN1YnRyZWUgKG9yXG4vLyBzdWJmb3Jlc3QpLiBJdCByZXR1cm5zIHRoZSBzdWNjZXNzb3Igb2YgdiBvbiB0aGlzIGNvbnRvdXIuIFRoaXMgc3VjY2Vzc29yIGlzXG4vLyBlaXRoZXIgZ2l2ZW4gYnkgdGhlIGxlZnRtb3N0IGNoaWxkIG9mIHYgb3IgYnkgdGhlIHRocmVhZCBvZiB2LiBUaGUgZnVuY3Rpb25cbi8vIHJldHVybnMgbnVsbCBpZiBhbmQgb25seSBpZiB2IGlzIG9uIHRoZSBoaWdoZXN0IGxldmVsIG9mIGl0cyBzdWJ0cmVlLlxuZnVuY3Rpb24gbmV4dExlZnQodikge1xuICB2YXIgY2hpbGRyZW4gPSB2LmNoaWxkcmVuO1xuICByZXR1cm4gY2hpbGRyZW4gPyBjaGlsZHJlblswXSA6IHYudDtcbn1cblxuLy8gVGhpcyBmdW5jdGlvbiB3b3JrcyBhbmFsb2dvdXNseSB0byBuZXh0TGVmdC5cbmZ1bmN0aW9uIG5leHRSaWdodCh2KSB7XG4gIHZhciBjaGlsZHJlbiA9IHYuY2hpbGRyZW47XG4gIHJldHVybiBjaGlsZHJlbiA/IGNoaWxkcmVuW2NoaWxkcmVuLmxlbmd0aCAtIDFdIDogdi50O1xufVxuXG4vLyBTaGlmdHMgdGhlIGN1cnJlbnQgc3VidHJlZSByb290ZWQgYXQgdysuIFRoaXMgaXMgZG9uZSBieSBpbmNyZWFzaW5nXG4vLyBwcmVsaW0odyspIGFuZCBtb2QodyspIGJ5IHNoaWZ0LlxuZnVuY3Rpb24gbW92ZVN1YnRyZWUod20sIHdwLCBzaGlmdCkge1xuICB2YXIgY2hhbmdlID0gc2hpZnQgLyAod3AuaSAtIHdtLmkpO1xuICB3cC5jIC09IGNoYW5nZTtcbiAgd3AucyArPSBzaGlmdDtcbiAgd20uYyArPSBjaGFuZ2U7XG4gIHdwLnogKz0gc2hpZnQ7XG4gIHdwLm0gKz0gc2hpZnQ7XG59XG5cbi8vIEFsbCBvdGhlciBzaGlmdHMsIGFwcGxpZWQgdG8gdGhlIHNtYWxsZXIgc3VidHJlZXMgYmV0d2VlbiB3LSBhbmQgdyssIGFyZVxuLy8gcGVyZm9ybWVkIGJ5IHRoaXMgZnVuY3Rpb24uIFRvIHByZXBhcmUgdGhlIHNoaWZ0cywgd2UgaGF2ZSB0byBhZGp1c3Rcbi8vIGNoYW5nZSh3KyksIHNoaWZ0KHcrKSwgYW5kIGNoYW5nZSh3LSkuXG5mdW5jdGlvbiBleGVjdXRlU2hpZnRzKHYpIHtcbiAgdmFyIHNoaWZ0ID0gMCxcbiAgICAgIGNoYW5nZSA9IDAsXG4gICAgICBjaGlsZHJlbiA9IHYuY2hpbGRyZW4sXG4gICAgICBpID0gY2hpbGRyZW4ubGVuZ3RoLFxuICAgICAgdztcbiAgd2hpbGUgKC0taSA+PSAwKSB7XG4gICAgdyA9IGNoaWxkcmVuW2ldO1xuICAgIHcueiArPSBzaGlmdDtcbiAgICB3Lm0gKz0gc2hpZnQ7XG4gICAgc2hpZnQgKz0gdy5zICsgKGNoYW5nZSArPSB3LmMpO1xuICB9XG59XG5cbi8vIElmIHZpLeKAmXMgYW5jZXN0b3IgaXMgYSBzaWJsaW5nIG9mIHYsIHJldHVybnMgdmkt4oCZcyBhbmNlc3Rvci4gT3RoZXJ3aXNlLFxuLy8gcmV0dXJucyB0aGUgc3BlY2lmaWVkIChkZWZhdWx0KSBhbmNlc3Rvci5cbmZ1bmN0aW9uIG5leHRBbmNlc3Rvcih2aW0sIHYsIGFuY2VzdG9yKSB7XG4gIHJldHVybiB2aW0uYS5wYXJlbnQgPT09IHYucGFyZW50ID8gdmltLmEgOiBhbmNlc3Rvcjtcbn1cblxuZnVuY3Rpb24gVHJlZU5vZGUobm9kZSwgaSkge1xuICB0aGlzLl8gPSBub2RlO1xuICB0aGlzLnBhcmVudCA9IG51bGw7XG4gIHRoaXMuY2hpbGRyZW4gPSBudWxsO1xuICB0aGlzLkEgPSBudWxsOyAvLyBkZWZhdWx0IGFuY2VzdG9yXG4gIHRoaXMuYSA9IHRoaXM7IC8vIGFuY2VzdG9yXG4gIHRoaXMueiA9IDA7IC8vIHByZWxpbVxuICB0aGlzLm0gPSAwOyAvLyBtb2RcbiAgdGhpcy5jID0gMDsgLy8gY2hhbmdlXG4gIHRoaXMucyA9IDA7IC8vIHNoaWZ0XG4gIHRoaXMudCA9IG51bGw7IC8vIHRocmVhZFxuICB0aGlzLmkgPSBpOyAvLyBudW1iZXJcbn1cblxuVHJlZU5vZGUucHJvdG90eXBlID0gT2JqZWN0LmNyZWF0ZShOb2RlLnByb3RvdHlwZSk7XG5cbmZ1bmN0aW9uIHRyZWVSb290KHJvb3QpIHtcbiAgdmFyIHRyZWUgPSBuZXcgVHJlZU5vZGUocm9vdCwgMCksXG4gICAgICBub2RlLFxuICAgICAgbm9kZXMgPSBbdHJlZV0sXG4gICAgICBjaGlsZCxcbiAgICAgIGNoaWxkcmVuLFxuICAgICAgaSxcbiAgICAgIG47XG5cbiAgd2hpbGUgKG5vZGUgPSBub2Rlcy5wb3AoKSkge1xuICAgIGlmIChjaGlsZHJlbiA9IG5vZGUuXy5jaGlsZHJlbikge1xuICAgICAgbm9kZS5jaGlsZHJlbiA9IG5ldyBBcnJheShuID0gY2hpbGRyZW4ubGVuZ3RoKTtcbiAgICAgIGZvciAoaSA9IG4gLSAxOyBpID49IDA7IC0taSkge1xuICAgICAgICBub2Rlcy5wdXNoKGNoaWxkID0gbm9kZS5jaGlsZHJlbltpXSA9IG5ldyBUcmVlTm9kZShjaGlsZHJlbltpXSwgaSkpO1xuICAgICAgICBjaGlsZC5wYXJlbnQgPSBub2RlO1xuICAgICAgfVxuICAgIH1cbiAgfVxuXG4gICh0cmVlLnBhcmVudCA9IG5ldyBUcmVlTm9kZShudWxsLCAwKSkuY2hpbGRyZW4gPSBbdHJlZV07XG4gIHJldHVybiB0cmVlO1xufVxuXG4vLyBOb2RlLWxpbmsgdHJlZSBkaWFncmFtIHVzaW5nIHRoZSBSZWluZ29sZC1UaWxmb3JkIFwidGlkeVwiIGFsZ29yaXRobVxuZXhwb3J0IGRlZmF1bHQgZnVuY3Rpb24oKSB7XG4gIHZhciBzZXBhcmF0aW9uID0gZGVmYXVsdFNlcGFyYXRpb24sXG4gICAgICBkeCA9IDEsXG4gICAgICBkeSA9IDEsXG4gICAgICBub2RlU2l6ZSA9IG51bGw7XG5cbiAgZnVuY3Rpb24gdHJlZShyb290KSB7XG4gICAgdmFyIHQgPSB0cmVlUm9vdChyb290KTtcblxuICAgIC8vIENvbXB1dGUgdGhlIGxheW91dCB1c2luZyBCdWNoaGVpbSBldCBhbC7igJlzIGFsZ29yaXRobS5cbiAgICB0LmVhY2hBZnRlcihmaXJzdFdhbGspLCB0LnBhcmVudC5tID0gLXQuejtcbiAgICB0LmVhY2hCZWZvcmUoc2Vjb25kV2Fsayk7XG5cbiAgICAvLyBJZiBhIGZpeGVkIG5vZGUgc2l6ZSBpcyBzcGVjaWZpZWQsIHNjYWxlIHggYW5kIHkuXG4gICAgaWYgKG5vZGVTaXplKSByb290LmVhY2hCZWZvcmUoc2l6ZU5vZGUpO1xuXG4gICAgLy8gSWYgYSBmaXhlZCB0cmVlIHNpemUgaXMgc3BlY2lmaWVkLCBzY2FsZSB4IGFuZCB5IGJhc2VkIG9uIHRoZSBleHRlbnQuXG4gICAgLy8gQ29tcHV0ZSB0aGUgbGVmdC1tb3N0LCByaWdodC1tb3N0LCBhbmQgZGVwdGgtbW9zdCBub2RlcyBmb3IgZXh0ZW50cy5cbiAgICBlbHNlIHtcbiAgICAgIHZhciBsZWZ0ID0gcm9vdCxcbiAgICAgICAgICByaWdodCA9IHJvb3QsXG4gICAgICAgICAgYm90dG9tID0gcm9vdDtcbiAgICAgIHJvb3QuZWFjaEJlZm9yZShmdW5jdGlvbihub2RlKSB7XG4gICAgICAgIGlmIChub2RlLnggPCBsZWZ0LngpIGxlZnQgPSBub2RlO1xuICAgICAgICBpZiAobm9kZS54ID4gcmlnaHQueCkgcmlnaHQgPSBub2RlO1xuICAgICAgICBpZiAobm9kZS5kZXB0aCA+IGJvdHRvbS5kZXB0aCkgYm90dG9tID0gbm9kZTtcbiAgICAgIH0pO1xuICAgICAgdmFyIHMgPSBsZWZ0ID09PSByaWdodCA/IDEgOiBzZXBhcmF0aW9uKGxlZnQsIHJpZ2h0KSAvIDIsXG4gICAgICAgICAgdHggPSBzIC0gbGVmdC54LFxuICAgICAgICAgIGt4ID0gZHggLyAocmlnaHQueCArIHMgKyB0eCksXG4gICAgICAgICAga3kgPSBkeSAvIChib3R0b20uZGVwdGggfHwgMSk7XG4gICAgICByb290LmVhY2hCZWZvcmUoZnVuY3Rpb24obm9kZSkge1xuICAgICAgICBub2RlLnggPSAobm9kZS54ICsgdHgpICoga3g7XG4gICAgICAgIG5vZGUueSA9IG5vZGUuZGVwdGggKiBreTtcbiAgICAgIH0pO1xuICAgIH1cblxuICAgIHJldHVybiByb290O1xuICB9XG5cbiAgLy8gQ29tcHV0ZXMgYSBwcmVsaW1pbmFyeSB4LWNvb3JkaW5hdGUgZm9yIHYuIEJlZm9yZSB0aGF0LCBGSVJTVCBXQUxLIGlzXG4gIC8vIGFwcGxpZWQgcmVjdXJzaXZlbHkgdG8gdGhlIGNoaWxkcmVuIG9mIHYsIGFzIHdlbGwgYXMgdGhlIGZ1bmN0aW9uXG4gIC8vIEFQUE9SVElPTi4gQWZ0ZXIgc3BhY2luZyBvdXQgdGhlIGNoaWxkcmVuIGJ5IGNhbGxpbmcgRVhFQ1VURSBTSElGVFMsIHRoZVxuICAvLyBub2RlIHYgaXMgcGxhY2VkIHRvIHRoZSBtaWRwb2ludCBvZiBpdHMgb3V0ZXJtb3N0IGNoaWxkcmVuLlxuICBmdW5jdGlvbiBmaXJzdFdhbGsodikge1xuICAgIHZhciBjaGlsZHJlbiA9IHYuY2hpbGRyZW4sXG4gICAgICAgIHNpYmxpbmdzID0gdi5wYXJlbnQuY2hpbGRyZW4sXG4gICAgICAgIHcgPSB2LmkgPyBzaWJsaW5nc1t2LmkgLSAxXSA6IG51bGw7XG4gICAgaWYgKGNoaWxkcmVuKSB7XG4gICAgICBleGVjdXRlU2hpZnRzKHYpO1xuICAgICAgdmFyIG1pZHBvaW50ID0gKGNoaWxkcmVuWzBdLnogKyBjaGlsZHJlbltjaGlsZHJlbi5sZW5ndGggLSAxXS56KSAvIDI7XG4gICAgICBpZiAodykge1xuICAgICAgICB2LnogPSB3LnogKyBzZXBhcmF0aW9uKHYuXywgdy5fKTtcbiAgICAgICAgdi5tID0gdi56IC0gbWlkcG9pbnQ7XG4gICAgICB9IGVsc2Uge1xuICAgICAgICB2LnogPSBtaWRwb2ludDtcbiAgICAgIH1cbiAgICB9IGVsc2UgaWYgKHcpIHtcbiAgICAgIHYueiA9IHcueiArIHNlcGFyYXRpb24odi5fLCB3Ll8pO1xuICAgIH1cbiAgICB2LnBhcmVudC5BID0gYXBwb3J0aW9uKHYsIHcsIHYucGFyZW50LkEgfHwgc2libGluZ3NbMF0pO1xuICB9XG5cbiAgLy8gQ29tcHV0ZXMgYWxsIHJlYWwgeC1jb29yZGluYXRlcyBieSBzdW1taW5nIHVwIHRoZSBtb2RpZmllcnMgcmVjdXJzaXZlbHkuXG4gIGZ1bmN0aW9uIHNlY29uZFdhbGsodikge1xuICAgIHYuXy54ID0gdi56ICsgdi5wYXJlbnQubTtcbiAgICB2Lm0gKz0gdi5wYXJlbnQubTtcbiAgfVxuXG4gIC8vIFRoZSBjb3JlIG9mIHRoZSBhbGdvcml0aG0uIEhlcmUsIGEgbmV3IHN1YnRyZWUgaXMgY29tYmluZWQgd2l0aCB0aGVcbiAgLy8gcHJldmlvdXMgc3VidHJlZXMuIFRocmVhZHMgYXJlIHVzZWQgdG8gdHJhdmVyc2UgdGhlIGluc2lkZSBhbmQgb3V0c2lkZVxuICAvLyBjb250b3VycyBvZiB0aGUgbGVmdCBhbmQgcmlnaHQgc3VidHJlZSB1cCB0byB0aGUgaGlnaGVzdCBjb21tb24gbGV2ZWwuIFRoZVxuICAvLyB2ZXJ0aWNlcyB1c2VkIGZvciB0aGUgdHJhdmVyc2FscyBhcmUgdmkrLCB2aS0sIHZvLSwgYW5kIHZvKywgd2hlcmUgdGhlXG4gIC8vIHN1cGVyc2NyaXB0IG8gbWVhbnMgb3V0c2lkZSBhbmQgaSBtZWFucyBpbnNpZGUsIHRoZSBzdWJzY3JpcHQgLSBtZWFucyBsZWZ0XG4gIC8vIHN1YnRyZWUgYW5kICsgbWVhbnMgcmlnaHQgc3VidHJlZS4gRm9yIHN1bW1pbmcgdXAgdGhlIG1vZGlmaWVycyBhbG9uZyB0aGVcbiAgLy8gY29udG91ciwgd2UgdXNlIHJlc3BlY3RpdmUgdmFyaWFibGVzIHNpKywgc2ktLCBzby0sIGFuZCBzbysuIFdoZW5ldmVyIHR3b1xuICAvLyBub2RlcyBvZiB0aGUgaW5zaWRlIGNvbnRvdXJzIGNvbmZsaWN0LCB3ZSBjb21wdXRlIHRoZSBsZWZ0IG9uZSBvZiB0aGVcbiAgLy8gZ3JlYXRlc3QgdW5jb21tb24gYW5jZXN0b3JzIHVzaW5nIHRoZSBmdW5jdGlvbiBBTkNFU1RPUiBhbmQgY2FsbCBNT1ZFXG4gIC8vIFNVQlRSRUUgdG8gc2hpZnQgdGhlIHN1YnRyZWUgYW5kIHByZXBhcmUgdGhlIHNoaWZ0cyBvZiBzbWFsbGVyIHN1YnRyZWVzLlxuICAvLyBGaW5hbGx5LCB3ZSBhZGQgYSBuZXcgdGhyZWFkIChpZiBuZWNlc3NhcnkpLlxuICBmdW5jdGlvbiBhcHBvcnRpb24odiwgdywgYW5jZXN0b3IpIHtcbiAgICBpZiAodykge1xuICAgICAgdmFyIHZpcCA9IHYsXG4gICAgICAgICAgdm9wID0gdixcbiAgICAgICAgICB2aW0gPSB3LFxuICAgICAgICAgIHZvbSA9IHZpcC5wYXJlbnQuY2hpbGRyZW5bMF0sXG4gICAgICAgICAgc2lwID0gdmlwLm0sXG4gICAgICAgICAgc29wID0gdm9wLm0sXG4gICAgICAgICAgc2ltID0gdmltLm0sXG4gICAgICAgICAgc29tID0gdm9tLm0sXG4gICAgICAgICAgc2hpZnQ7XG4gICAgICB3aGlsZSAodmltID0gbmV4dFJpZ2h0KHZpbSksIHZpcCA9IG5leHRMZWZ0KHZpcCksIHZpbSAmJiB2aXApIHtcbiAgICAgICAgdm9tID0gbmV4dExlZnQodm9tKTtcbiAgICAgICAgdm9wID0gbmV4dFJpZ2h0KHZvcCk7XG4gICAgICAgIHZvcC5hID0gdjtcbiAgICAgICAgc2hpZnQgPSB2aW0ueiArIHNpbSAtIHZpcC56IC0gc2lwICsgc2VwYXJhdGlvbih2aW0uXywgdmlwLl8pO1xuICAgICAgICBpZiAoc2hpZnQgPiAwKSB7XG4gICAgICAgICAgbW92ZVN1YnRyZWUobmV4dEFuY2VzdG9yKHZpbSwgdiwgYW5jZXN0b3IpLCB2LCBzaGlmdCk7XG4gICAgICAgICAgc2lwICs9IHNoaWZ0O1xuICAgICAgICAgIHNvcCArPSBzaGlmdDtcbiAgICAgICAgfVxuICAgICAgICBzaW0gKz0gdmltLm07XG4gICAgICAgIHNpcCArPSB2aXAubTtcbiAgICAgICAgc29tICs9IHZvbS5tO1xuICAgICAgICBzb3AgKz0gdm9wLm07XG4gICAgICB9XG4gICAgICBpZiAodmltICYmICFuZXh0UmlnaHQodm9wKSkge1xuICAgICAgICB2b3AudCA9IHZpbTtcbiAgICAgICAgdm9wLm0gKz0gc2ltIC0gc29wO1xuICAgICAgfVxuICAgICAgaWYgKHZpcCAmJiAhbmV4dExlZnQodm9tKSkge1xuICAgICAgICB2b20udCA9IHZpcDtcbiAgICAgICAgdm9tLm0gKz0gc2lwIC0gc29tO1xuICAgICAgICBhbmNlc3RvciA9IHY7XG4gICAgICB9XG4gICAgfVxuICAgIHJldHVybiBhbmNlc3RvcjtcbiAgfVxuXG4gIGZ1bmN0aW9uIHNpemVOb2RlKG5vZGUpIHtcbiAgICBub2RlLnggKj0gZHg7XG4gICAgbm9kZS55ID0gbm9kZS5kZXB0aCAqIGR5O1xuICB9XG5cbiAgdHJlZS5zZXBhcmF0aW9uID0gZnVuY3Rpb24oeCkge1xuICAgIHJldHVybiBhcmd1bWVudHMubGVuZ3RoID8gKHNlcGFyYXRpb24gPSB4LCB0cmVlKSA6IHNlcGFyYXRpb247XG4gIH07XG5cbiAgdHJlZS5zaXplID0gZnVuY3Rpb24oeCkge1xuICAgIHJldHVybiBhcmd1bWVudHMubGVuZ3RoID8gKG5vZGVTaXplID0gZmFsc2UsIGR4ID0gK3hbMF0sIGR5ID0gK3hbMV0sIHRyZWUpIDogKG5vZGVTaXplID8gbnVsbCA6IFtkeCwgZHldKTtcbiAgfTtcblxuICB0cmVlLm5vZGVTaXplID0gZnVuY3Rpb24oeCkge1xuICAgIHJldHVybiBhcmd1bWVudHMubGVuZ3RoID8gKG5vZGVTaXplID0gdHJ1ZSwgZHggPSAreFswXSwgZHkgPSAreFsxXSwgdHJlZSkgOiAobm9kZVNpemUgPyBbZHgsIGR5XSA6IG51bGwpO1xuICB9O1xuXG4gIHJldHVybiB0cmVlO1xufVxuIiwiZXhwb3J0IHZhciB4aHRtbCA9IFwiaHR0cDovL3d3dy53My5vcmcvMTk5OS94aHRtbFwiO1xuXG5leHBvcnQgZGVmYXVsdCB7XG4gIHN2ZzogXCJodHRwOi8vd3d3LnczLm9yZy8yMDAwL3N2Z1wiLFxuICB4aHRtbDogeGh0bWwsXG4gIHhsaW5rOiBcImh0dHA6Ly93d3cudzMub3JnLzE5OTkveGxpbmtcIixcbiAgeG1sOiBcImh0dHA6Ly93d3cudzMub3JnL1hNTC8xOTk4L25hbWVzcGFjZVwiLFxuICB4bWxuczogXCJodHRwOi8vd3d3LnczLm9yZy8yMDAwL3htbG5zL1wiXG59O1xuIiwiaW1wb3J0IG5hbWVzcGFjZXMgZnJvbSBcIi4vbmFtZXNwYWNlcy5qc1wiO1xuXG5leHBvcnQgZGVmYXVsdCBmdW5jdGlvbihuYW1lKSB7XG4gIHZhciBwcmVmaXggPSBuYW1lICs9IFwiXCIsIGkgPSBwcmVmaXguaW5kZXhPZihcIjpcIik7XG4gIGlmIChpID49IDAgJiYgKHByZWZpeCA9IG5hbWUuc2xpY2UoMCwgaSkpICE9PSBcInhtbG5zXCIpIG5hbWUgPSBuYW1lLnNsaWNlKGkgKyAxKTtcbiAgcmV0dXJuIG5hbWVzcGFjZXMuaGFzT3duUHJvcGVydHkocHJlZml4KSA/IHtzcGFjZTogbmFtZXNwYWNlc1twcmVmaXhdLCBsb2NhbDogbmFtZX0gOiBuYW1lOyAvLyBlc2xpbnQtZGlzYWJsZS1saW5lIG5vLXByb3RvdHlwZS1idWlsdGluc1xufVxuIiwiaW1wb3J0IG5hbWVzcGFjZSBmcm9tIFwiLi9uYW1lc3BhY2UuanNcIjtcbmltcG9ydCB7eGh0bWx9IGZyb20gXCIuL25hbWVzcGFjZXMuanNcIjtcblxuZnVuY3Rpb24gY3JlYXRvckluaGVyaXQobmFtZSkge1xuICByZXR1cm4gZnVuY3Rpb24oKSB7XG4gICAgdmFyIGRvY3VtZW50ID0gdGhpcy5vd25lckRvY3VtZW50LFxuICAgICAgICB1cmkgPSB0aGlzLm5hbWVzcGFjZVVSSTtcbiAgICByZXR1cm4gdXJpID09PSB4aHRtbCAmJiBkb2N1bWVudC5kb2N1bWVudEVsZW1lbnQubmFtZXNwYWNlVVJJID09PSB4aHRtbFxuICAgICAgICA/IGRvY3VtZW50LmNyZWF0ZUVsZW1lbnQobmFtZSlcbiAgICAgICAgOiBkb2N1bWVudC5jcmVhdGVFbGVtZW50TlModXJpLCBuYW1lKTtcbiAgfTtcbn1cblxuZnVuY3Rpb24gY3JlYXRvckZpeGVkKGZ1bGxuYW1lKSB7XG4gIHJldHVybiBmdW5jdGlvbigpIHtcbiAgICByZXR1cm4gdGhpcy5vd25lckRvY3VtZW50LmNyZWF0ZUVsZW1lbnROUyhmdWxsbmFtZS5zcGFjZSwgZnVsbG5hbWUubG9jYWwpO1xuICB9O1xufVxuXG5leHBvcnQgZGVmYXVsdCBmdW5jdGlvbihuYW1lKSB7XG4gIHZhciBmdWxsbmFtZSA9IG5hbWVzcGFjZShuYW1lKTtcbiAgcmV0dXJuIChmdWxsbmFtZS5sb2NhbFxuICAgICAgPyBjcmVhdG9yRml4ZWRcbiAgICAgIDogY3JlYXRvckluaGVyaXQpKGZ1bGxuYW1lKTtcbn1cbiIsImZ1bmN0aW9uIG5vbmUoKSB7fVxuXG5leHBvcnQgZGVmYXVsdCBmdW5jdGlvbihzZWxlY3Rvcikge1xuICByZXR1cm4gc2VsZWN0b3IgPT0gbnVsbCA/IG5vbmUgOiBmdW5jdGlvbigpIHtcbiAgICByZXR1cm4gdGhpcy5xdWVyeVNlbGVjdG9yKHNlbGVjdG9yKTtcbiAgfTtcbn1cbiIsImltcG9ydCB7U2VsZWN0aW9ufSBmcm9tIFwiLi9pbmRleC5qc1wiO1xuaW1wb3J0IHNlbGVjdG9yIGZyb20gXCIuLi9zZWxlY3Rvci5qc1wiO1xuXG5leHBvcnQgZGVmYXVsdCBmdW5jdGlvbihzZWxlY3QpIHtcbiAgaWYgKHR5cGVvZiBzZWxlY3QgIT09IFwiZnVuY3Rpb25cIikgc2VsZWN0ID0gc2VsZWN0b3Ioc2VsZWN0KTtcblxuICBmb3IgKHZhciBncm91cHMgPSB0aGlzLl9ncm91cHMsIG0gPSBncm91cHMubGVuZ3RoLCBzdWJncm91cHMgPSBuZXcgQXJyYXkobSksIGogPSAwOyBqIDwgbTsgKytqKSB7XG4gICAgZm9yICh2YXIgZ3JvdXAgPSBncm91cHNbal0sIG4gPSBncm91cC5sZW5ndGgsIHN1Ymdyb3VwID0gc3ViZ3JvdXBzW2pdID0gbmV3IEFycmF5KG4pLCBub2RlLCBzdWJub2RlLCBpID0gMDsgaSA8IG47ICsraSkge1xuICAgICAgaWYgKChub2RlID0gZ3JvdXBbaV0pICYmIChzdWJub2RlID0gc2VsZWN0LmNhbGwobm9kZSwgbm9kZS5fX2RhdGFfXywgaSwgZ3JvdXApKSkge1xuICAgICAgICBpZiAoXCJfX2RhdGFfX1wiIGluIG5vZGUpIHN1Ym5vZGUuX19kYXRhX18gPSBub2RlLl9fZGF0YV9fO1xuICAgICAgICBzdWJncm91cFtpXSA9IHN1Ym5vZGU7XG4gICAgICB9XG4gICAgfVxuICB9XG5cbiAgcmV0dXJuIG5ldyBTZWxlY3Rpb24oc3ViZ3JvdXBzLCB0aGlzLl9wYXJlbnRzKTtcbn1cbiIsIi8vIEdpdmVuIHNvbWV0aGluZyBhcnJheSBsaWtlIChvciBudWxsKSwgcmV0dXJucyBzb21ldGhpbmcgdGhhdCBpcyBzdHJpY3RseSBhblxuLy8gYXJyYXkuIFRoaXMgaXMgdXNlZCB0byBlbnN1cmUgdGhhdCBhcnJheS1saWtlIG9iamVjdHMgcGFzc2VkIHRvIGQzLnNlbGVjdEFsbFxuLy8gb3Igc2VsZWN0aW9uLnNlbGVjdEFsbCBhcmUgY29udmVydGVkIGludG8gcHJvcGVyIGFycmF5cyB3aGVuIGNyZWF0aW5nIGFcbi8vIHNlbGVjdGlvbjsgd2UgZG9u4oCZdCBldmVyIHdhbnQgdG8gY3JlYXRlIGEgc2VsZWN0aW9uIGJhY2tlZCBieSBhIGxpdmVcbi8vIEhUTUxDb2xsZWN0aW9uIG9yIE5vZGVMaXN0LiBIb3dldmVyLCBub3RlIHRoYXQgc2VsZWN0aW9uLnNlbGVjdEFsbCB3aWxsIHVzZSBhXG4vLyBzdGF0aWMgTm9kZUxpc3QgYXMgYSBncm91cCwgc2luY2UgaXQgc2FmZWx5IGRlcml2ZWQgZnJvbSBxdWVyeVNlbGVjdG9yQWxsLlxuZXhwb3J0IGRlZmF1bHQgZnVuY3Rpb24gYXJyYXkoeCkge1xuICByZXR1cm4geCA9PSBudWxsID8gW10gOiBBcnJheS5pc0FycmF5KHgpID8geCA6IEFycmF5LmZyb20oeCk7XG59XG4iLCJmdW5jdGlvbiBlbXB0eSgpIHtcbiAgcmV0dXJuIFtdO1xufVxuXG5leHBvcnQgZGVmYXVsdCBmdW5jdGlvbihzZWxlY3Rvcikge1xuICByZXR1cm4gc2VsZWN0b3IgPT0gbnVsbCA/IGVtcHR5IDogZnVuY3Rpb24oKSB7XG4gICAgcmV0dXJuIHRoaXMucXVlcnlTZWxlY3RvckFsbChzZWxlY3Rvcik7XG4gIH07XG59XG4iLCJpbXBvcnQge1NlbGVjdGlvbn0gZnJvbSBcIi4vaW5kZXguanNcIjtcbmltcG9ydCBhcnJheSBmcm9tIFwiLi4vYXJyYXkuanNcIjtcbmltcG9ydCBzZWxlY3RvckFsbCBmcm9tIFwiLi4vc2VsZWN0b3JBbGwuanNcIjtcblxuZnVuY3Rpb24gYXJyYXlBbGwoc2VsZWN0KSB7XG4gIHJldHVybiBmdW5jdGlvbigpIHtcbiAgICByZXR1cm4gYXJyYXkoc2VsZWN0LmFwcGx5KHRoaXMsIGFyZ3VtZW50cykpO1xuICB9O1xufVxuXG5leHBvcnQgZGVmYXVsdCBmdW5jdGlvbihzZWxlY3QpIHtcbiAgaWYgKHR5cGVvZiBzZWxlY3QgPT09IFwiZnVuY3Rpb25cIikgc2VsZWN0ID0gYXJyYXlBbGwoc2VsZWN0KTtcbiAgZWxzZSBzZWxlY3QgPSBzZWxlY3RvckFsbChzZWxlY3QpO1xuXG4gIGZvciAodmFyIGdyb3VwcyA9IHRoaXMuX2dyb3VwcywgbSA9IGdyb3Vwcy5sZW5ndGgsIHN1Ymdyb3VwcyA9IFtdLCBwYXJlbnRzID0gW10sIGogPSAwOyBqIDwgbTsgKytqKSB7XG4gICAgZm9yICh2YXIgZ3JvdXAgPSBncm91cHNbal0sIG4gPSBncm91cC5sZW5ndGgsIG5vZGUsIGkgPSAwOyBpIDwgbjsgKytpKSB7XG4gICAgICBpZiAobm9kZSA9IGdyb3VwW2ldKSB7XG4gICAgICAgIHN1Ymdyb3Vwcy5wdXNoKHNlbGVjdC5jYWxsKG5vZGUsIG5vZGUuX19kYXRhX18sIGksIGdyb3VwKSk7XG4gICAgICAgIHBhcmVudHMucHVzaChub2RlKTtcbiAgICAgIH1cbiAgICB9XG4gIH1cblxuICByZXR1cm4gbmV3IFNlbGVjdGlvbihzdWJncm91cHMsIHBhcmVudHMpO1xufVxuIiwiZXhwb3J0IGRlZmF1bHQgZnVuY3Rpb24oc2VsZWN0b3IpIHtcbiAgcmV0dXJuIGZ1bmN0aW9uKCkge1xuICAgIHJldHVybiB0aGlzLm1hdGNoZXMoc2VsZWN0b3IpO1xuICB9O1xufVxuXG5leHBvcnQgZnVuY3Rpb24gY2hpbGRNYXRjaGVyKHNlbGVjdG9yKSB7XG4gIHJldHVybiBmdW5jdGlvbihub2RlKSB7XG4gICAgcmV0dXJuIG5vZGUubWF0Y2hlcyhzZWxlY3Rvcik7XG4gIH07XG59XG5cbiIsImltcG9ydCB7Y2hpbGRNYXRjaGVyfSBmcm9tIFwiLi4vbWF0Y2hlci5qc1wiO1xuXG52YXIgZmluZCA9IEFycmF5LnByb3RvdHlwZS5maW5kO1xuXG5mdW5jdGlvbiBjaGlsZEZpbmQobWF0Y2gpIHtcbiAgcmV0dXJuIGZ1bmN0aW9uKCkge1xuICAgIHJldHVybiBmaW5kLmNhbGwodGhpcy5jaGlsZHJlbiwgbWF0Y2gpO1xuICB9O1xufVxuXG5mdW5jdGlvbiBjaGlsZEZpcnN0KCkge1xuICByZXR1cm4gdGhpcy5maXJzdEVsZW1lbnRDaGlsZDtcbn1cblxuZXhwb3J0IGRlZmF1bHQgZnVuY3Rpb24obWF0Y2gpIHtcbiAgcmV0dXJuIHRoaXMuc2VsZWN0KG1hdGNoID09IG51bGwgPyBjaGlsZEZpcnN0XG4gICAgICA6IGNoaWxkRmluZCh0eXBlb2YgbWF0Y2ggPT09IFwiZnVuY3Rpb25cIiA/IG1hdGNoIDogY2hpbGRNYXRjaGVyKG1hdGNoKSkpO1xufVxuIiwiaW1wb3J0IHtjaGlsZE1hdGNoZXJ9IGZyb20gXCIuLi9tYXRjaGVyLmpzXCI7XG5cbnZhciBmaWx0ZXIgPSBBcnJheS5wcm90b3R5cGUuZmlsdGVyO1xuXG5mdW5jdGlvbiBjaGlsZHJlbigpIHtcbiAgcmV0dXJuIEFycmF5LmZyb20odGhpcy5jaGlsZHJlbik7XG59XG5cbmZ1bmN0aW9uIGNoaWxkcmVuRmlsdGVyKG1hdGNoKSB7XG4gIHJldHVybiBmdW5jdGlvbigpIHtcbiAgICByZXR1cm4gZmlsdGVyLmNhbGwodGhpcy5jaGlsZHJlbiwgbWF0Y2gpO1xuICB9O1xufVxuXG5leHBvcnQgZGVmYXVsdCBmdW5jdGlvbihtYXRjaCkge1xuICByZXR1cm4gdGhpcy5zZWxlY3RBbGwobWF0Y2ggPT0gbnVsbCA/IGNoaWxkcmVuXG4gICAgICA6IGNoaWxkcmVuRmlsdGVyKHR5cGVvZiBtYXRjaCA9PT0gXCJmdW5jdGlvblwiID8gbWF0Y2ggOiBjaGlsZE1hdGNoZXIobWF0Y2gpKSk7XG59XG4iLCJpbXBvcnQge1NlbGVjdGlvbn0gZnJvbSBcIi4vaW5kZXguanNcIjtcbmltcG9ydCBtYXRjaGVyIGZyb20gXCIuLi9tYXRjaGVyLmpzXCI7XG5cbmV4cG9ydCBkZWZhdWx0IGZ1bmN0aW9uKG1hdGNoKSB7XG4gIGlmICh0eXBlb2YgbWF0Y2ggIT09IFwiZnVuY3Rpb25cIikgbWF0Y2ggPSBtYXRjaGVyKG1hdGNoKTtcblxuICBmb3IgKHZhciBncm91cHMgPSB0aGlzLl9ncm91cHMsIG0gPSBncm91cHMubGVuZ3RoLCBzdWJncm91cHMgPSBuZXcgQXJyYXkobSksIGogPSAwOyBqIDwgbTsgKytqKSB7XG4gICAgZm9yICh2YXIgZ3JvdXAgPSBncm91cHNbal0sIG4gPSBncm91cC5sZW5ndGgsIHN1Ymdyb3VwID0gc3ViZ3JvdXBzW2pdID0gW10sIG5vZGUsIGkgPSAwOyBpIDwgbjsgKytpKSB7XG4gICAgICBpZiAoKG5vZGUgPSBncm91cFtpXSkgJiYgbWF0Y2guY2FsbChub2RlLCBub2RlLl9fZGF0YV9fLCBpLCBncm91cCkpIHtcbiAgICAgICAgc3ViZ3JvdXAucHVzaChub2RlKTtcbiAgICAgIH1cbiAgICB9XG4gIH1cblxuICByZXR1cm4gbmV3IFNlbGVjdGlvbihzdWJncm91cHMsIHRoaXMuX3BhcmVudHMpO1xufVxuIiwiZXhwb3J0IGRlZmF1bHQgZnVuY3Rpb24odXBkYXRlKSB7XG4gIHJldHVybiBuZXcgQXJyYXkodXBkYXRlLmxlbmd0aCk7XG59XG4iLCJpbXBvcnQgc3BhcnNlIGZyb20gXCIuL3NwYXJzZS5qc1wiO1xuaW1wb3J0IHtTZWxlY3Rpb259IGZyb20gXCIuL2luZGV4LmpzXCI7XG5cbmV4cG9ydCBkZWZhdWx0IGZ1bmN0aW9uKCkge1xuICByZXR1cm4gbmV3IFNlbGVjdGlvbih0aGlzLl9lbnRlciB8fCB0aGlzLl9ncm91cHMubWFwKHNwYXJzZSksIHRoaXMuX3BhcmVudHMpO1xufVxuXG5leHBvcnQgZnVuY3Rpb24gRW50ZXJOb2RlKHBhcmVudCwgZGF0dW0pIHtcbiAgdGhpcy5vd25lckRvY3VtZW50ID0gcGFyZW50Lm93bmVyRG9jdW1lbnQ7XG4gIHRoaXMubmFtZXNwYWNlVVJJID0gcGFyZW50Lm5hbWVzcGFjZVVSSTtcbiAgdGhpcy5fbmV4dCA9IG51bGw7XG4gIHRoaXMuX3BhcmVudCA9IHBhcmVudDtcbiAgdGhpcy5fX2RhdGFfXyA9IGRhdHVtO1xufVxuXG5FbnRlck5vZGUucHJvdG90eXBlID0ge1xuICBjb25zdHJ1Y3RvcjogRW50ZXJOb2RlLFxuICBhcHBlbmRDaGlsZDogZnVuY3Rpb24oY2hpbGQpIHsgcmV0dXJuIHRoaXMuX3BhcmVudC5pbnNlcnRCZWZvcmUoY2hpbGQsIHRoaXMuX25leHQpOyB9LFxuICBpbnNlcnRCZWZvcmU6IGZ1bmN0aW9uKGNoaWxkLCBuZXh0KSB7IHJldHVybiB0aGlzLl9wYXJlbnQuaW5zZXJ0QmVmb3JlKGNoaWxkLCBuZXh0KTsgfSxcbiAgcXVlcnlTZWxlY3RvcjogZnVuY3Rpb24oc2VsZWN0b3IpIHsgcmV0dXJuIHRoaXMuX3BhcmVudC5xdWVyeVNlbGVjdG9yKHNlbGVjdG9yKTsgfSxcbiAgcXVlcnlTZWxlY3RvckFsbDogZnVuY3Rpb24oc2VsZWN0b3IpIHsgcmV0dXJuIHRoaXMuX3BhcmVudC5xdWVyeVNlbGVjdG9yQWxsKHNlbGVjdG9yKTsgfVxufTtcbiIsImV4cG9ydCBkZWZhdWx0IGZ1bmN0aW9uKHgpIHtcbiAgcmV0dXJuIGZ1bmN0aW9uKCkge1xuICAgIHJldHVybiB4O1xuICB9O1xufVxuIiwiaW1wb3J0IHtTZWxlY3Rpb259IGZyb20gXCIuL2luZGV4LmpzXCI7XG5pbXBvcnQge0VudGVyTm9kZX0gZnJvbSBcIi4vZW50ZXIuanNcIjtcbmltcG9ydCBjb25zdGFudCBmcm9tIFwiLi4vY29uc3RhbnQuanNcIjtcblxuZnVuY3Rpb24gYmluZEluZGV4KHBhcmVudCwgZ3JvdXAsIGVudGVyLCB1cGRhdGUsIGV4aXQsIGRhdGEpIHtcbiAgdmFyIGkgPSAwLFxuICAgICAgbm9kZSxcbiAgICAgIGdyb3VwTGVuZ3RoID0gZ3JvdXAubGVuZ3RoLFxuICAgICAgZGF0YUxlbmd0aCA9IGRhdGEubGVuZ3RoO1xuXG4gIC8vIFB1dCBhbnkgbm9uLW51bGwgbm9kZXMgdGhhdCBmaXQgaW50byB1cGRhdGUuXG4gIC8vIFB1dCBhbnkgbnVsbCBub2RlcyBpbnRvIGVudGVyLlxuICAvLyBQdXQgYW55IHJlbWFpbmluZyBkYXRhIGludG8gZW50ZXIuXG4gIGZvciAoOyBpIDwgZGF0YUxlbmd0aDsgKytpKSB7XG4gICAgaWYgKG5vZGUgPSBncm91cFtpXSkge1xuICAgICAgbm9kZS5fX2RhdGFfXyA9IGRhdGFbaV07XG4gICAgICB1cGRhdGVbaV0gPSBub2RlO1xuICAgIH0gZWxzZSB7XG4gICAgICBlbnRlcltpXSA9IG5ldyBFbnRlck5vZGUocGFyZW50LCBkYXRhW2ldKTtcbiAgICB9XG4gIH1cblxuICAvLyBQdXQgYW55IG5vbi1udWxsIG5vZGVzIHRoYXQgZG9u4oCZdCBmaXQgaW50byBleGl0LlxuICBmb3IgKDsgaSA8IGdyb3VwTGVuZ3RoOyArK2kpIHtcbiAgICBpZiAobm9kZSA9IGdyb3VwW2ldKSB7XG4gICAgICBleGl0W2ldID0gbm9kZTtcbiAgICB9XG4gIH1cbn1cblxuZnVuY3Rpb24gYmluZEtleShwYXJlbnQsIGdyb3VwLCBlbnRlciwgdXBkYXRlLCBleGl0LCBkYXRhLCBrZXkpIHtcbiAgdmFyIGksXG4gICAgICBub2RlLFxuICAgICAgbm9kZUJ5S2V5VmFsdWUgPSBuZXcgTWFwLFxuICAgICAgZ3JvdXBMZW5ndGggPSBncm91cC5sZW5ndGgsXG4gICAgICBkYXRhTGVuZ3RoID0gZGF0YS5sZW5ndGgsXG4gICAgICBrZXlWYWx1ZXMgPSBuZXcgQXJyYXkoZ3JvdXBMZW5ndGgpLFxuICAgICAga2V5VmFsdWU7XG5cbiAgLy8gQ29tcHV0ZSB0aGUga2V5IGZvciBlYWNoIG5vZGUuXG4gIC8vIElmIG11bHRpcGxlIG5vZGVzIGhhdmUgdGhlIHNhbWUga2V5LCB0aGUgZHVwbGljYXRlcyBhcmUgYWRkZWQgdG8gZXhpdC5cbiAgZm9yIChpID0gMDsgaSA8IGdyb3VwTGVuZ3RoOyArK2kpIHtcbiAgICBpZiAobm9kZSA9IGdyb3VwW2ldKSB7XG4gICAgICBrZXlWYWx1ZXNbaV0gPSBrZXlWYWx1ZSA9IGtleS5jYWxsKG5vZGUsIG5vZGUuX19kYXRhX18sIGksIGdyb3VwKSArIFwiXCI7XG4gICAgICBpZiAobm9kZUJ5S2V5VmFsdWUuaGFzKGtleVZhbHVlKSkge1xuICAgICAgICBleGl0W2ldID0gbm9kZTtcbiAgICAgIH0gZWxzZSB7XG4gICAgICAgIG5vZGVCeUtleVZhbHVlLnNldChrZXlWYWx1ZSwgbm9kZSk7XG4gICAgICB9XG4gICAgfVxuICB9XG5cbiAgLy8gQ29tcHV0ZSB0aGUga2V5IGZvciBlYWNoIGRhdHVtLlxuICAvLyBJZiB0aGVyZSBhIG5vZGUgYXNzb2NpYXRlZCB3aXRoIHRoaXMga2V5LCBqb2luIGFuZCBhZGQgaXQgdG8gdXBkYXRlLlxuICAvLyBJZiB0aGVyZSBpcyBub3QgKG9yIHRoZSBrZXkgaXMgYSBkdXBsaWNhdGUpLCBhZGQgaXQgdG8gZW50ZXIuXG4gIGZvciAoaSA9IDA7IGkgPCBkYXRhTGVuZ3RoOyArK2kpIHtcbiAgICBrZXlWYWx1ZSA9IGtleS5jYWxsKHBhcmVudCwgZGF0YVtpXSwgaSwgZGF0YSkgKyBcIlwiO1xuICAgIGlmIChub2RlID0gbm9kZUJ5S2V5VmFsdWUuZ2V0KGtleVZhbHVlKSkge1xuICAgICAgdXBkYXRlW2ldID0gbm9kZTtcbiAgICAgIG5vZGUuX19kYXRhX18gPSBkYXRhW2ldO1xuICAgICAgbm9kZUJ5S2V5VmFsdWUuZGVsZXRlKGtleVZhbHVlKTtcbiAgICB9IGVsc2Uge1xuICAgICAgZW50ZXJbaV0gPSBuZXcgRW50ZXJOb2RlKHBhcmVudCwgZGF0YVtpXSk7XG4gICAgfVxuICB9XG5cbiAgLy8gQWRkIGFueSByZW1haW5pbmcgbm9kZXMgdGhhdCB3ZXJlIG5vdCBib3VuZCB0byBkYXRhIHRvIGV4aXQuXG4gIGZvciAoaSA9IDA7IGkgPCBncm91cExlbmd0aDsgKytpKSB7XG4gICAgaWYgKChub2RlID0gZ3JvdXBbaV0pICYmIChub2RlQnlLZXlWYWx1ZS5nZXQoa2V5VmFsdWVzW2ldKSA9PT0gbm9kZSkpIHtcbiAgICAgIGV4aXRbaV0gPSBub2RlO1xuICAgIH1cbiAgfVxufVxuXG5mdW5jdGlvbiBkYXR1bShub2RlKSB7XG4gIHJldHVybiBub2RlLl9fZGF0YV9fO1xufVxuXG5leHBvcnQgZGVmYXVsdCBmdW5jdGlvbih2YWx1ZSwga2V5KSB7XG4gIGlmICghYXJndW1lbnRzLmxlbmd0aCkgcmV0dXJuIEFycmF5LmZyb20odGhpcywgZGF0dW0pO1xuXG4gIHZhciBiaW5kID0ga2V5ID8gYmluZEtleSA6IGJpbmRJbmRleCxcbiAgICAgIHBhcmVudHMgPSB0aGlzLl9wYXJlbnRzLFxuICAgICAgZ3JvdXBzID0gdGhpcy5fZ3JvdXBzO1xuXG4gIGlmICh0eXBlb2YgdmFsdWUgIT09IFwiZnVuY3Rpb25cIikgdmFsdWUgPSBjb25zdGFudCh2YWx1ZSk7XG5cbiAgZm9yICh2YXIgbSA9IGdyb3Vwcy5sZW5ndGgsIHVwZGF0ZSA9IG5ldyBBcnJheShtKSwgZW50ZXIgPSBuZXcgQXJyYXkobSksIGV4aXQgPSBuZXcgQXJyYXkobSksIGogPSAwOyBqIDwgbTsgKytqKSB7XG4gICAgdmFyIHBhcmVudCA9IHBhcmVudHNbal0sXG4gICAgICAgIGdyb3VwID0gZ3JvdXBzW2pdLFxuICAgICAgICBncm91cExlbmd0aCA9IGdyb3VwLmxlbmd0aCxcbiAgICAgICAgZGF0YSA9IGFycmF5bGlrZSh2YWx1ZS5jYWxsKHBhcmVudCwgcGFyZW50ICYmIHBhcmVudC5fX2RhdGFfXywgaiwgcGFyZW50cykpLFxuICAgICAgICBkYXRhTGVuZ3RoID0gZGF0YS5sZW5ndGgsXG4gICAgICAgIGVudGVyR3JvdXAgPSBlbnRlcltqXSA9IG5ldyBBcnJheShkYXRhTGVuZ3RoKSxcbiAgICAgICAgdXBkYXRlR3JvdXAgPSB1cGRhdGVbal0gPSBuZXcgQXJyYXkoZGF0YUxlbmd0aCksXG4gICAgICAgIGV4aXRHcm91cCA9IGV4aXRbal0gPSBuZXcgQXJyYXkoZ3JvdXBMZW5ndGgpO1xuXG4gICAgYmluZChwYXJlbnQsIGdyb3VwLCBlbnRlckdyb3VwLCB1cGRhdGVHcm91cCwgZXhpdEdyb3VwLCBkYXRhLCBrZXkpO1xuXG4gICAgLy8gTm93IGNvbm5lY3QgdGhlIGVudGVyIG5vZGVzIHRvIHRoZWlyIGZvbGxvd2luZyB1cGRhdGUgbm9kZSwgc3VjaCB0aGF0XG4gICAgLy8gYXBwZW5kQ2hpbGQgY2FuIGluc2VydCB0aGUgbWF0ZXJpYWxpemVkIGVudGVyIG5vZGUgYmVmb3JlIHRoaXMgbm9kZSxcbiAgICAvLyByYXRoZXIgdGhhbiBhdCB0aGUgZW5kIG9mIHRoZSBwYXJlbnQgbm9kZS5cbiAgICBmb3IgKHZhciBpMCA9IDAsIGkxID0gMCwgcHJldmlvdXMsIG5leHQ7IGkwIDwgZGF0YUxlbmd0aDsgKytpMCkge1xuICAgICAgaWYgKHByZXZpb3VzID0gZW50ZXJHcm91cFtpMF0pIHtcbiAgICAgICAgaWYgKGkwID49IGkxKSBpMSA9IGkwICsgMTtcbiAgICAgICAgd2hpbGUgKCEobmV4dCA9IHVwZGF0ZUdyb3VwW2kxXSkgJiYgKytpMSA8IGRhdGFMZW5ndGgpO1xuICAgICAgICBwcmV2aW91cy5fbmV4dCA9IG5leHQgfHwgbnVsbDtcbiAgICAgIH1cbiAgICB9XG4gIH1cblxuICB1cGRhdGUgPSBuZXcgU2VsZWN0aW9uKHVwZGF0ZSwgcGFyZW50cyk7XG4gIHVwZGF0ZS5fZW50ZXIgPSBlbnRlcjtcbiAgdXBkYXRlLl9leGl0ID0gZXhpdDtcbiAgcmV0dXJuIHVwZGF0ZTtcbn1cblxuLy8gR2l2ZW4gc29tZSBkYXRhLCB0aGlzIHJldHVybnMgYW4gYXJyYXktbGlrZSB2aWV3IG9mIGl0OiBhbiBvYmplY3QgdGhhdFxuLy8gZXhwb3NlcyBhIGxlbmd0aCBwcm9wZXJ0eSBhbmQgYWxsb3dzIG51bWVyaWMgaW5kZXhpbmcuIE5vdGUgdGhhdCB1bmxpa2Vcbi8vIHNlbGVjdEFsbCwgdGhpcyBpc27igJl0IHdvcnJpZWQgYWJvdXQg4oCcbGl2ZeKAnSBjb2xsZWN0aW9ucyBiZWNhdXNlIHRoZSByZXN1bHRpbmdcbi8vIGFycmF5IHdpbGwgb25seSBiZSB1c2VkIGJyaWVmbHkgd2hpbGUgZGF0YSBpcyBiZWluZyBib3VuZC4gKEl0IGlzIHBvc3NpYmxlIHRvXG4vLyBjYXVzZSB0aGUgZGF0YSB0byBjaGFuZ2Ugd2hpbGUgaXRlcmF0aW5nIGJ5IHVzaW5nIGEga2V5IGZ1bmN0aW9uLCBidXQgcGxlYXNlXG4vLyBkb27igJl0OyB3ZeKAmWQgcmF0aGVyIGF2b2lkIGEgZ3JhdHVpdG91cyBjb3B5LilcbmZ1bmN0aW9uIGFycmF5bGlrZShkYXRhKSB7XG4gIHJldHVybiB0eXBlb2YgZGF0YSA9PT0gXCJvYmplY3RcIiAmJiBcImxlbmd0aFwiIGluIGRhdGFcbiAgICA/IGRhdGEgLy8gQXJyYXksIFR5cGVkQXJyYXksIE5vZGVMaXN0LCBhcnJheS1saWtlXG4gICAgOiBBcnJheS5mcm9tKGRhdGEpOyAvLyBNYXAsIFNldCwgaXRlcmFibGUsIHN0cmluZywgb3IgYW55dGhpbmcgZWxzZVxufVxuIiwiaW1wb3J0IHNwYXJzZSBmcm9tIFwiLi9zcGFyc2UuanNcIjtcbmltcG9ydCB7U2VsZWN0aW9ufSBmcm9tIFwiLi9pbmRleC5qc1wiO1xuXG5leHBvcnQgZGVmYXVsdCBmdW5jdGlvbigpIHtcbiAgcmV0dXJuIG5ldyBTZWxlY3Rpb24odGhpcy5fZXhpdCB8fCB0aGlzLl9ncm91cHMubWFwKHNwYXJzZSksIHRoaXMuX3BhcmVudHMpO1xufVxuIiwiZXhwb3J0IGRlZmF1bHQgZnVuY3Rpb24ob25lbnRlciwgb251cGRhdGUsIG9uZXhpdCkge1xuICB2YXIgZW50ZXIgPSB0aGlzLmVudGVyKCksIHVwZGF0ZSA9IHRoaXMsIGV4aXQgPSB0aGlzLmV4aXQoKTtcbiAgaWYgKHR5cGVvZiBvbmVudGVyID09PSBcImZ1bmN0aW9uXCIpIHtcbiAgICBlbnRlciA9IG9uZW50ZXIoZW50ZXIpO1xuICAgIGlmIChlbnRlcikgZW50ZXIgPSBlbnRlci5zZWxlY3Rpb24oKTtcbiAgfSBlbHNlIHtcbiAgICBlbnRlciA9IGVudGVyLmFwcGVuZChvbmVudGVyICsgXCJcIik7XG4gIH1cbiAgaWYgKG9udXBkYXRlICE9IG51bGwpIHtcbiAgICB1cGRhdGUgPSBvbnVwZGF0ZSh1cGRhdGUpO1xuICAgIGlmICh1cGRhdGUpIHVwZGF0ZSA9IHVwZGF0ZS5zZWxlY3Rpb24oKTtcbiAgfVxuICBpZiAob25leGl0ID09IG51bGwpIGV4aXQucmVtb3ZlKCk7IGVsc2Ugb25leGl0KGV4aXQpO1xuICByZXR1cm4gZW50ZXIgJiYgdXBkYXRlID8gZW50ZXIubWVyZ2UodXBkYXRlKS5vcmRlcigpIDogdXBkYXRlO1xufVxuIiwiaW1wb3J0IHtTZWxlY3Rpb259IGZyb20gXCIuL2luZGV4LmpzXCI7XG5cbmV4cG9ydCBkZWZhdWx0IGZ1bmN0aW9uKGNvbnRleHQpIHtcbiAgdmFyIHNlbGVjdGlvbiA9IGNvbnRleHQuc2VsZWN0aW9uID8gY29udGV4dC5zZWxlY3Rpb24oKSA6IGNvbnRleHQ7XG5cbiAgZm9yICh2YXIgZ3JvdXBzMCA9IHRoaXMuX2dyb3VwcywgZ3JvdXBzMSA9IHNlbGVjdGlvbi5fZ3JvdXBzLCBtMCA9IGdyb3VwczAubGVuZ3RoLCBtMSA9IGdyb3VwczEubGVuZ3RoLCBtID0gTWF0aC5taW4obTAsIG0xKSwgbWVyZ2VzID0gbmV3IEFycmF5KG0wKSwgaiA9IDA7IGogPCBtOyArK2opIHtcbiAgICBmb3IgKHZhciBncm91cDAgPSBncm91cHMwW2pdLCBncm91cDEgPSBncm91cHMxW2pdLCBuID0gZ3JvdXAwLmxlbmd0aCwgbWVyZ2UgPSBtZXJnZXNbal0gPSBuZXcgQXJyYXkobiksIG5vZGUsIGkgPSAwOyBpIDwgbjsgKytpKSB7XG4gICAgICBpZiAobm9kZSA9IGdyb3VwMFtpXSB8fCBncm91cDFbaV0pIHtcbiAgICAgICAgbWVyZ2VbaV0gPSBub2RlO1xuICAgICAgfVxuICAgIH1cbiAgfVxuXG4gIGZvciAoOyBqIDwgbTA7ICsraikge1xuICAgIG1lcmdlc1tqXSA9IGdyb3VwczBbal07XG4gIH1cblxuICByZXR1cm4gbmV3IFNlbGVjdGlvbihtZXJnZXMsIHRoaXMuX3BhcmVudHMpO1xufVxuIiwiZXhwb3J0IGRlZmF1bHQgZnVuY3Rpb24oKSB7XG5cbiAgZm9yICh2YXIgZ3JvdXBzID0gdGhpcy5fZ3JvdXBzLCBqID0gLTEsIG0gPSBncm91cHMubGVuZ3RoOyArK2ogPCBtOykge1xuICAgIGZvciAodmFyIGdyb3VwID0gZ3JvdXBzW2pdLCBpID0gZ3JvdXAubGVuZ3RoIC0gMSwgbmV4dCA9IGdyb3VwW2ldLCBub2RlOyAtLWkgPj0gMDspIHtcbiAgICAgIGlmIChub2RlID0gZ3JvdXBbaV0pIHtcbiAgICAgICAgaWYgKG5leHQgJiYgbm9kZS5jb21wYXJlRG9jdW1lbnRQb3NpdGlvbihuZXh0KSBeIDQpIG5leHQucGFyZW50Tm9kZS5pbnNlcnRCZWZvcmUobm9kZSwgbmV4dCk7XG4gICAgICAgIG5leHQgPSBub2RlO1xuICAgICAgfVxuICAgIH1cbiAgfVxuXG4gIHJldHVybiB0aGlzO1xufVxuIiwiaW1wb3J0IHtTZWxlY3Rpb259IGZyb20gXCIuL2luZGV4LmpzXCI7XG5cbmV4cG9ydCBkZWZhdWx0IGZ1bmN0aW9uKGNvbXBhcmUpIHtcbiAgaWYgKCFjb21wYXJlKSBjb21wYXJlID0gYXNjZW5kaW5nO1xuXG4gIGZ1bmN0aW9uIGNvbXBhcmVOb2RlKGEsIGIpIHtcbiAgICByZXR1cm4gYSAmJiBiID8gY29tcGFyZShhLl9fZGF0YV9fLCBiLl9fZGF0YV9fKSA6ICFhIC0gIWI7XG4gIH1cblxuICBmb3IgKHZhciBncm91cHMgPSB0aGlzLl9ncm91cHMsIG0gPSBncm91cHMubGVuZ3RoLCBzb3J0Z3JvdXBzID0gbmV3IEFycmF5KG0pLCBqID0gMDsgaiA8IG07ICsraikge1xuICAgIGZvciAodmFyIGdyb3VwID0gZ3JvdXBzW2pdLCBuID0gZ3JvdXAubGVuZ3RoLCBzb3J0Z3JvdXAgPSBzb3J0Z3JvdXBzW2pdID0gbmV3IEFycmF5KG4pLCBub2RlLCBpID0gMDsgaSA8IG47ICsraSkge1xuICAgICAgaWYgKG5vZGUgPSBncm91cFtpXSkge1xuICAgICAgICBzb3J0Z3JvdXBbaV0gPSBub2RlO1xuICAgICAgfVxuICAgIH1cbiAgICBzb3J0Z3JvdXAuc29ydChjb21wYXJlTm9kZSk7XG4gIH1cblxuICByZXR1cm4gbmV3IFNlbGVjdGlvbihzb3J0Z3JvdXBzLCB0aGlzLl9wYXJlbnRzKS5vcmRlcigpO1xufVxuXG5mdW5jdGlvbiBhc2NlbmRpbmcoYSwgYikge1xuICByZXR1cm4gYSA8IGIgPyAtMSA6IGEgPiBiID8gMSA6IGEgPj0gYiA/IDAgOiBOYU47XG59XG4iLCJleHBvcnQgZGVmYXVsdCBmdW5jdGlvbigpIHtcbiAgdmFyIGNhbGxiYWNrID0gYXJndW1lbnRzWzBdO1xuICBhcmd1bWVudHNbMF0gPSB0aGlzO1xuICBjYWxsYmFjay5hcHBseShudWxsLCBhcmd1bWVudHMpO1xuICByZXR1cm4gdGhpcztcbn1cbiIsImV4cG9ydCBkZWZhdWx0IGZ1bmN0aW9uKCkge1xuICByZXR1cm4gQXJyYXkuZnJvbSh0aGlzKTtcbn1cbiIsImV4cG9ydCBkZWZhdWx0IGZ1bmN0aW9uKCkge1xuXG4gIGZvciAodmFyIGdyb3VwcyA9IHRoaXMuX2dyb3VwcywgaiA9IDAsIG0gPSBncm91cHMubGVuZ3RoOyBqIDwgbTsgKytqKSB7XG4gICAgZm9yICh2YXIgZ3JvdXAgPSBncm91cHNbal0sIGkgPSAwLCBuID0gZ3JvdXAubGVuZ3RoOyBpIDwgbjsgKytpKSB7XG4gICAgICB2YXIgbm9kZSA9IGdyb3VwW2ldO1xuICAgICAgaWYgKG5vZGUpIHJldHVybiBub2RlO1xuICAgIH1cbiAgfVxuXG4gIHJldHVybiBudWxsO1xufVxuIiwiZXhwb3J0IGRlZmF1bHQgZnVuY3Rpb24oKSB7XG4gIGxldCBzaXplID0gMDtcbiAgZm9yIChjb25zdCBub2RlIG9mIHRoaXMpICsrc2l6ZTsgLy8gZXNsaW50LWRpc2FibGUtbGluZSBuby11bnVzZWQtdmFyc1xuICByZXR1cm4gc2l6ZTtcbn1cbiIsImV4cG9ydCBkZWZhdWx0IGZ1bmN0aW9uKCkge1xuICByZXR1cm4gIXRoaXMubm9kZSgpO1xufVxuIiwiZXhwb3J0IGRlZmF1bHQgZnVuY3Rpb24oY2FsbGJhY2spIHtcblxuICBmb3IgKHZhciBncm91cHMgPSB0aGlzLl9ncm91cHMsIGogPSAwLCBtID0gZ3JvdXBzLmxlbmd0aDsgaiA8IG07ICsraikge1xuICAgIGZvciAodmFyIGdyb3VwID0gZ3JvdXBzW2pdLCBpID0gMCwgbiA9IGdyb3VwLmxlbmd0aCwgbm9kZTsgaSA8IG47ICsraSkge1xuICAgICAgaWYgKG5vZGUgPSBncm91cFtpXSkgY2FsbGJhY2suY2FsbChub2RlLCBub2RlLl9fZGF0YV9fLCBpLCBncm91cCk7XG4gICAgfVxuICB9XG5cbiAgcmV0dXJuIHRoaXM7XG59XG4iLCJpbXBvcnQgbmFtZXNwYWNlIGZyb20gXCIuLi9uYW1lc3BhY2UuanNcIjtcblxuZnVuY3Rpb24gYXR0clJlbW92ZShuYW1lKSB7XG4gIHJldHVybiBmdW5jdGlvbigpIHtcbiAgICB0aGlzLnJlbW92ZUF0dHJpYnV0ZShuYW1lKTtcbiAgfTtcbn1cblxuZnVuY3Rpb24gYXR0clJlbW92ZU5TKGZ1bGxuYW1lKSB7XG4gIHJldHVybiBmdW5jdGlvbigpIHtcbiAgICB0aGlzLnJlbW92ZUF0dHJpYnV0ZU5TKGZ1bGxuYW1lLnNwYWNlLCBmdWxsbmFtZS5sb2NhbCk7XG4gIH07XG59XG5cbmZ1bmN0aW9uIGF0dHJDb25zdGFudChuYW1lLCB2YWx1ZSkge1xuICByZXR1cm4gZnVuY3Rpb24oKSB7XG4gICAgdGhpcy5zZXRBdHRyaWJ1dGUobmFtZSwgdmFsdWUpO1xuICB9O1xufVxuXG5mdW5jdGlvbiBhdHRyQ29uc3RhbnROUyhmdWxsbmFtZSwgdmFsdWUpIHtcbiAgcmV0dXJuIGZ1bmN0aW9uKCkge1xuICAgIHRoaXMuc2V0QXR0cmlidXRlTlMoZnVsbG5hbWUuc3BhY2UsIGZ1bGxuYW1lLmxvY2FsLCB2YWx1ZSk7XG4gIH07XG59XG5cbmZ1bmN0aW9uIGF0dHJGdW5jdGlvbihuYW1lLCB2YWx1ZSkge1xuICByZXR1cm4gZnVuY3Rpb24oKSB7XG4gICAgdmFyIHYgPSB2YWx1ZS5hcHBseSh0aGlzLCBhcmd1bWVudHMpO1xuICAgIGlmICh2ID09IG51bGwpIHRoaXMucmVtb3ZlQXR0cmlidXRlKG5hbWUpO1xuICAgIGVsc2UgdGhpcy5zZXRBdHRyaWJ1dGUobmFtZSwgdik7XG4gIH07XG59XG5cbmZ1bmN0aW9uIGF0dHJGdW5jdGlvbk5TKGZ1bGxuYW1lLCB2YWx1ZSkge1xuICByZXR1cm4gZnVuY3Rpb24oKSB7XG4gICAgdmFyIHYgPSB2YWx1ZS5hcHBseSh0aGlzLCBhcmd1bWVudHMpO1xuICAgIGlmICh2ID09IG51bGwpIHRoaXMucmVtb3ZlQXR0cmlidXRlTlMoZnVsbG5hbWUuc3BhY2UsIGZ1bGxuYW1lLmxvY2FsKTtcbiAgICBlbHNlIHRoaXMuc2V0QXR0cmlidXRlTlMoZnVsbG5hbWUuc3BhY2UsIGZ1bGxuYW1lLmxvY2FsLCB2KTtcbiAgfTtcbn1cblxuZXhwb3J0IGRlZmF1bHQgZnVuY3Rpb24obmFtZSwgdmFsdWUpIHtcbiAgdmFyIGZ1bGxuYW1lID0gbmFtZXNwYWNlKG5hbWUpO1xuXG4gIGlmIChhcmd1bWVudHMubGVuZ3RoIDwgMikge1xuICAgIHZhciBub2RlID0gdGhpcy5ub2RlKCk7XG4gICAgcmV0dXJuIGZ1bGxuYW1lLmxvY2FsXG4gICAgICAgID8gbm9kZS5nZXRBdHRyaWJ1dGVOUyhmdWxsbmFtZS5zcGFjZSwgZnVsbG5hbWUubG9jYWwpXG4gICAgICAgIDogbm9kZS5nZXRBdHRyaWJ1dGUoZnVsbG5hbWUpO1xuICB9XG5cbiAgcmV0dXJuIHRoaXMuZWFjaCgodmFsdWUgPT0gbnVsbFxuICAgICAgPyAoZnVsbG5hbWUubG9jYWwgPyBhdHRyUmVtb3ZlTlMgOiBhdHRyUmVtb3ZlKSA6ICh0eXBlb2YgdmFsdWUgPT09IFwiZnVuY3Rpb25cIlxuICAgICAgPyAoZnVsbG5hbWUubG9jYWwgPyBhdHRyRnVuY3Rpb25OUyA6IGF0dHJGdW5jdGlvbilcbiAgICAgIDogKGZ1bGxuYW1lLmxvY2FsID8gYXR0ckNvbnN0YW50TlMgOiBhdHRyQ29uc3RhbnQpKSkoZnVsbG5hbWUsIHZhbHVlKSk7XG59XG4iLCJleHBvcnQgZGVmYXVsdCBmdW5jdGlvbihub2RlKSB7XG4gIHJldHVybiAobm9kZS5vd25lckRvY3VtZW50ICYmIG5vZGUub3duZXJEb2N1bWVudC5kZWZhdWx0VmlldykgLy8gbm9kZSBpcyBhIE5vZGVcbiAgICAgIHx8IChub2RlLmRvY3VtZW50ICYmIG5vZGUpIC8vIG5vZGUgaXMgYSBXaW5kb3dcbiAgICAgIHx8IG5vZGUuZGVmYXVsdFZpZXc7IC8vIG5vZGUgaXMgYSBEb2N1bWVudFxufVxuIiwiaW1wb3J0IGRlZmF1bHRWaWV3IGZyb20gXCIuLi93aW5kb3cuanNcIjtcblxuZnVuY3Rpb24gc3R5bGVSZW1vdmUobmFtZSkge1xuICByZXR1cm4gZnVuY3Rpb24oKSB7XG4gICAgdGhpcy5zdHlsZS5yZW1vdmVQcm9wZXJ0eShuYW1lKTtcbiAgfTtcbn1cblxuZnVuY3Rpb24gc3R5bGVDb25zdGFudChuYW1lLCB2YWx1ZSwgcHJpb3JpdHkpIHtcbiAgcmV0dXJuIGZ1bmN0aW9uKCkge1xuICAgIHRoaXMuc3R5bGUuc2V0UHJvcGVydHkobmFtZSwgdmFsdWUsIHByaW9yaXR5KTtcbiAgfTtcbn1cblxuZnVuY3Rpb24gc3R5bGVGdW5jdGlvbihuYW1lLCB2YWx1ZSwgcHJpb3JpdHkpIHtcbiAgcmV0dXJuIGZ1bmN0aW9uKCkge1xuICAgIHZhciB2ID0gdmFsdWUuYXBwbHkodGhpcywgYXJndW1lbnRzKTtcbiAgICBpZiAodiA9PSBudWxsKSB0aGlzLnN0eWxlLnJlbW92ZVByb3BlcnR5KG5hbWUpO1xuICAgIGVsc2UgdGhpcy5zdHlsZS5zZXRQcm9wZXJ0eShuYW1lLCB2LCBwcmlvcml0eSk7XG4gIH07XG59XG5cbmV4cG9ydCBkZWZhdWx0IGZ1bmN0aW9uKG5hbWUsIHZhbHVlLCBwcmlvcml0eSkge1xuICByZXR1cm4gYXJndW1lbnRzLmxlbmd0aCA+IDFcbiAgICAgID8gdGhpcy5lYWNoKCh2YWx1ZSA9PSBudWxsXG4gICAgICAgICAgICA/IHN0eWxlUmVtb3ZlIDogdHlwZW9mIHZhbHVlID09PSBcImZ1bmN0aW9uXCJcbiAgICAgICAgICAgID8gc3R5bGVGdW5jdGlvblxuICAgICAgICAgICAgOiBzdHlsZUNvbnN0YW50KShuYW1lLCB2YWx1ZSwgcHJpb3JpdHkgPT0gbnVsbCA/IFwiXCIgOiBwcmlvcml0eSkpXG4gICAgICA6IHN0eWxlVmFsdWUodGhpcy5ub2RlKCksIG5hbWUpO1xufVxuXG5leHBvcnQgZnVuY3Rpb24gc3R5bGVWYWx1ZShub2RlLCBuYW1lKSB7XG4gIHJldHVybiBub2RlLnN0eWxlLmdldFByb3BlcnR5VmFsdWUobmFtZSlcbiAgICAgIHx8IGRlZmF1bHRWaWV3KG5vZGUpLmdldENvbXB1dGVkU3R5bGUobm9kZSwgbnVsbCkuZ2V0UHJvcGVydHlWYWx1ZShuYW1lKTtcbn1cbiIsImZ1bmN0aW9uIHByb3BlcnR5UmVtb3ZlKG5hbWUpIHtcbiAgcmV0dXJuIGZ1bmN0aW9uKCkge1xuICAgIGRlbGV0ZSB0aGlzW25hbWVdO1xuICB9O1xufVxuXG5mdW5jdGlvbiBwcm9wZXJ0eUNvbnN0YW50KG5hbWUsIHZhbHVlKSB7XG4gIHJldHVybiBmdW5jdGlvbigpIHtcbiAgICB0aGlzW25hbWVdID0gdmFsdWU7XG4gIH07XG59XG5cbmZ1bmN0aW9uIHByb3BlcnR5RnVuY3Rpb24obmFtZSwgdmFsdWUpIHtcbiAgcmV0dXJuIGZ1bmN0aW9uKCkge1xuICAgIHZhciB2ID0gdmFsdWUuYXBwbHkodGhpcywgYXJndW1lbnRzKTtcbiAgICBpZiAodiA9PSBudWxsKSBkZWxldGUgdGhpc1tuYW1lXTtcbiAgICBlbHNlIHRoaXNbbmFtZV0gPSB2O1xuICB9O1xufVxuXG5leHBvcnQgZGVmYXVsdCBmdW5jdGlvbihuYW1lLCB2YWx1ZSkge1xuICByZXR1cm4gYXJndW1lbnRzLmxlbmd0aCA+IDFcbiAgICAgID8gdGhpcy5lYWNoKCh2YWx1ZSA9PSBudWxsXG4gICAgICAgICAgPyBwcm9wZXJ0eVJlbW92ZSA6IHR5cGVvZiB2YWx1ZSA9PT0gXCJmdW5jdGlvblwiXG4gICAgICAgICAgPyBwcm9wZXJ0eUZ1bmN0aW9uXG4gICAgICAgICAgOiBwcm9wZXJ0eUNvbnN0YW50KShuYW1lLCB2YWx1ZSkpXG4gICAgICA6IHRoaXMubm9kZSgpW25hbWVdO1xufVxuIiwiZnVuY3Rpb24gY2xhc3NBcnJheShzdHJpbmcpIHtcbiAgcmV0dXJuIHN0cmluZy50cmltKCkuc3BsaXQoL158XFxzKy8pO1xufVxuXG5mdW5jdGlvbiBjbGFzc0xpc3Qobm9kZSkge1xuICByZXR1cm4gbm9kZS5jbGFzc0xpc3QgfHwgbmV3IENsYXNzTGlzdChub2RlKTtcbn1cblxuZnVuY3Rpb24gQ2xhc3NMaXN0KG5vZGUpIHtcbiAgdGhpcy5fbm9kZSA9IG5vZGU7XG4gIHRoaXMuX25hbWVzID0gY2xhc3NBcnJheShub2RlLmdldEF0dHJpYnV0ZShcImNsYXNzXCIpIHx8IFwiXCIpO1xufVxuXG5DbGFzc0xpc3QucHJvdG90eXBlID0ge1xuICBhZGQ6IGZ1bmN0aW9uKG5hbWUpIHtcbiAgICB2YXIgaSA9IHRoaXMuX25hbWVzLmluZGV4T2YobmFtZSk7XG4gICAgaWYgKGkgPCAwKSB7XG4gICAgICB0aGlzLl9uYW1lcy5wdXNoKG5hbWUpO1xuICAgICAgdGhpcy5fbm9kZS5zZXRBdHRyaWJ1dGUoXCJjbGFzc1wiLCB0aGlzLl9uYW1lcy5qb2luKFwiIFwiKSk7XG4gICAgfVxuICB9LFxuICByZW1vdmU6IGZ1bmN0aW9uKG5hbWUpIHtcbiAgICB2YXIgaSA9IHRoaXMuX25hbWVzLmluZGV4T2YobmFtZSk7XG4gICAgaWYgKGkgPj0gMCkge1xuICAgICAgdGhpcy5fbmFtZXMuc3BsaWNlKGksIDEpO1xuICAgICAgdGhpcy5fbm9kZS5zZXRBdHRyaWJ1dGUoXCJjbGFzc1wiLCB0aGlzLl9uYW1lcy5qb2luKFwiIFwiKSk7XG4gICAgfVxuICB9LFxuICBjb250YWluczogZnVuY3Rpb24obmFtZSkge1xuICAgIHJldHVybiB0aGlzLl9uYW1lcy5pbmRleE9mKG5hbWUpID49IDA7XG4gIH1cbn07XG5cbmZ1bmN0aW9uIGNsYXNzZWRBZGQobm9kZSwgbmFtZXMpIHtcbiAgdmFyIGxpc3QgPSBjbGFzc0xpc3Qobm9kZSksIGkgPSAtMSwgbiA9IG5hbWVzLmxlbmd0aDtcbiAgd2hpbGUgKCsraSA8IG4pIGxpc3QuYWRkKG5hbWVzW2ldKTtcbn1cblxuZnVuY3Rpb24gY2xhc3NlZFJlbW92ZShub2RlLCBuYW1lcykge1xuICB2YXIgbGlzdCA9IGNsYXNzTGlzdChub2RlKSwgaSA9IC0xLCBuID0gbmFtZXMubGVuZ3RoO1xuICB3aGlsZSAoKytpIDwgbikgbGlzdC5yZW1vdmUobmFtZXNbaV0pO1xufVxuXG5mdW5jdGlvbiBjbGFzc2VkVHJ1ZShuYW1lcykge1xuICByZXR1cm4gZnVuY3Rpb24oKSB7XG4gICAgY2xhc3NlZEFkZCh0aGlzLCBuYW1lcyk7XG4gIH07XG59XG5cbmZ1bmN0aW9uIGNsYXNzZWRGYWxzZShuYW1lcykge1xuICByZXR1cm4gZnVuY3Rpb24oKSB7XG4gICAgY2xhc3NlZFJlbW92ZSh0aGlzLCBuYW1lcyk7XG4gIH07XG59XG5cbmZ1bmN0aW9uIGNsYXNzZWRGdW5jdGlvbihuYW1lcywgdmFsdWUpIHtcbiAgcmV0dXJuIGZ1bmN0aW9uKCkge1xuICAgICh2YWx1ZS5hcHBseSh0aGlzLCBhcmd1bWVudHMpID8gY2xhc3NlZEFkZCA6IGNsYXNzZWRSZW1vdmUpKHRoaXMsIG5hbWVzKTtcbiAgfTtcbn1cblxuZXhwb3J0IGRlZmF1bHQgZnVuY3Rpb24obmFtZSwgdmFsdWUpIHtcbiAgdmFyIG5hbWVzID0gY2xhc3NBcnJheShuYW1lICsgXCJcIik7XG5cbiAgaWYgKGFyZ3VtZW50cy5sZW5ndGggPCAyKSB7XG4gICAgdmFyIGxpc3QgPSBjbGFzc0xpc3QodGhpcy5ub2RlKCkpLCBpID0gLTEsIG4gPSBuYW1lcy5sZW5ndGg7XG4gICAgd2hpbGUgKCsraSA8IG4pIGlmICghbGlzdC5jb250YWlucyhuYW1lc1tpXSkpIHJldHVybiBmYWxzZTtcbiAgICByZXR1cm4gdHJ1ZTtcbiAgfVxuXG4gIHJldHVybiB0aGlzLmVhY2goKHR5cGVvZiB2YWx1ZSA9PT0gXCJmdW5jdGlvblwiXG4gICAgICA/IGNsYXNzZWRGdW5jdGlvbiA6IHZhbHVlXG4gICAgICA/IGNsYXNzZWRUcnVlXG4gICAgICA6IGNsYXNzZWRGYWxzZSkobmFtZXMsIHZhbHVlKSk7XG59XG4iLCJmdW5jdGlvbiB0ZXh0UmVtb3ZlKCkge1xuICB0aGlzLnRleHRDb250ZW50ID0gXCJcIjtcbn1cblxuZnVuY3Rpb24gdGV4dENvbnN0YW50KHZhbHVlKSB7XG4gIHJldHVybiBmdW5jdGlvbigpIHtcbiAgICB0aGlzLnRleHRDb250ZW50ID0gdmFsdWU7XG4gIH07XG59XG5cbmZ1bmN0aW9uIHRleHRGdW5jdGlvbih2YWx1ZSkge1xuICByZXR1cm4gZnVuY3Rpb24oKSB7XG4gICAgdmFyIHYgPSB2YWx1ZS5hcHBseSh0aGlzLCBhcmd1bWVudHMpO1xuICAgIHRoaXMudGV4dENvbnRlbnQgPSB2ID09IG51bGwgPyBcIlwiIDogdjtcbiAgfTtcbn1cblxuZXhwb3J0IGRlZmF1bHQgZnVuY3Rpb24odmFsdWUpIHtcbiAgcmV0dXJuIGFyZ3VtZW50cy5sZW5ndGhcbiAgICAgID8gdGhpcy5lYWNoKHZhbHVlID09IG51bGxcbiAgICAgICAgICA/IHRleHRSZW1vdmUgOiAodHlwZW9mIHZhbHVlID09PSBcImZ1bmN0aW9uXCJcbiAgICAgICAgICA/IHRleHRGdW5jdGlvblxuICAgICAgICAgIDogdGV4dENvbnN0YW50KSh2YWx1ZSkpXG4gICAgICA6IHRoaXMubm9kZSgpLnRleHRDb250ZW50O1xufVxuIiwiZnVuY3Rpb24gaHRtbFJlbW92ZSgpIHtcbiAgdGhpcy5pbm5lckhUTUwgPSBcIlwiO1xufVxuXG5mdW5jdGlvbiBodG1sQ29uc3RhbnQodmFsdWUpIHtcbiAgcmV0dXJuIGZ1bmN0aW9uKCkge1xuICAgIHRoaXMuaW5uZXJIVE1MID0gdmFsdWU7XG4gIH07XG59XG5cbmZ1bmN0aW9uIGh0bWxGdW5jdGlvbih2YWx1ZSkge1xuICByZXR1cm4gZnVuY3Rpb24oKSB7XG4gICAgdmFyIHYgPSB2YWx1ZS5hcHBseSh0aGlzLCBhcmd1bWVudHMpO1xuICAgIHRoaXMuaW5uZXJIVE1MID0gdiA9PSBudWxsID8gXCJcIiA6IHY7XG4gIH07XG59XG5cbmV4cG9ydCBkZWZhdWx0IGZ1bmN0aW9uKHZhbHVlKSB7XG4gIHJldHVybiBhcmd1bWVudHMubGVuZ3RoXG4gICAgICA/IHRoaXMuZWFjaCh2YWx1ZSA9PSBudWxsXG4gICAgICAgICAgPyBodG1sUmVtb3ZlIDogKHR5cGVvZiB2YWx1ZSA9PT0gXCJmdW5jdGlvblwiXG4gICAgICAgICAgPyBodG1sRnVuY3Rpb25cbiAgICAgICAgICA6IGh0bWxDb25zdGFudCkodmFsdWUpKVxuICAgICAgOiB0aGlzLm5vZGUoKS5pbm5lckhUTUw7XG59XG4iLCJmdW5jdGlvbiByYWlzZSgpIHtcbiAgaWYgKHRoaXMubmV4dFNpYmxpbmcpIHRoaXMucGFyZW50Tm9kZS5hcHBlbmRDaGlsZCh0aGlzKTtcbn1cblxuZXhwb3J0IGRlZmF1bHQgZnVuY3Rpb24oKSB7XG4gIHJldHVybiB0aGlzLmVhY2gocmFpc2UpO1xufVxuIiwiZnVuY3Rpb24gbG93ZXIoKSB7XG4gIGlmICh0aGlzLnByZXZpb3VzU2libGluZykgdGhpcy5wYXJlbnROb2RlLmluc2VydEJlZm9yZSh0aGlzLCB0aGlzLnBhcmVudE5vZGUuZmlyc3RDaGlsZCk7XG59XG5cbmV4cG9ydCBkZWZhdWx0IGZ1bmN0aW9uKCkge1xuICByZXR1cm4gdGhpcy5lYWNoKGxvd2VyKTtcbn1cbiIsImltcG9ydCBjcmVhdG9yIGZyb20gXCIuLi9jcmVhdG9yLmpzXCI7XG5cbmV4cG9ydCBkZWZhdWx0IGZ1bmN0aW9uKG5hbWUpIHtcbiAgdmFyIGNyZWF0ZSA9IHR5cGVvZiBuYW1lID09PSBcImZ1bmN0aW9uXCIgPyBuYW1lIDogY3JlYXRvcihuYW1lKTtcbiAgcmV0dXJuIHRoaXMuc2VsZWN0KGZ1bmN0aW9uKCkge1xuICAgIHJldHVybiB0aGlzLmFwcGVuZENoaWxkKGNyZWF0ZS5hcHBseSh0aGlzLCBhcmd1bWVudHMpKTtcbiAgfSk7XG59XG4iLCJpbXBvcnQgY3JlYXRvciBmcm9tIFwiLi4vY3JlYXRvci5qc1wiO1xuaW1wb3J0IHNlbGVjdG9yIGZyb20gXCIuLi9zZWxlY3Rvci5qc1wiO1xuXG5mdW5jdGlvbiBjb25zdGFudE51bGwoKSB7XG4gIHJldHVybiBudWxsO1xufVxuXG5leHBvcnQgZGVmYXVsdCBmdW5jdGlvbihuYW1lLCBiZWZvcmUpIHtcbiAgdmFyIGNyZWF0ZSA9IHR5cGVvZiBuYW1lID09PSBcImZ1bmN0aW9uXCIgPyBuYW1lIDogY3JlYXRvcihuYW1lKSxcbiAgICAgIHNlbGVjdCA9IGJlZm9yZSA9PSBudWxsID8gY29uc3RhbnROdWxsIDogdHlwZW9mIGJlZm9yZSA9PT0gXCJmdW5jdGlvblwiID8gYmVmb3JlIDogc2VsZWN0b3IoYmVmb3JlKTtcbiAgcmV0dXJuIHRoaXMuc2VsZWN0KGZ1bmN0aW9uKCkge1xuICAgIHJldHVybiB0aGlzLmluc2VydEJlZm9yZShjcmVhdGUuYXBwbHkodGhpcywgYXJndW1lbnRzKSwgc2VsZWN0LmFwcGx5KHRoaXMsIGFyZ3VtZW50cykgfHwgbnVsbCk7XG4gIH0pO1xufVxuIiwiZnVuY3Rpb24gcmVtb3ZlKCkge1xuICB2YXIgcGFyZW50ID0gdGhpcy5wYXJlbnROb2RlO1xuICBpZiAocGFyZW50KSBwYXJlbnQucmVtb3ZlQ2hpbGQodGhpcyk7XG59XG5cbmV4cG9ydCBkZWZhdWx0IGZ1bmN0aW9uKCkge1xuICByZXR1cm4gdGhpcy5lYWNoKHJlbW92ZSk7XG59XG4iLCJmdW5jdGlvbiBzZWxlY3Rpb25fY2xvbmVTaGFsbG93KCkge1xuICB2YXIgY2xvbmUgPSB0aGlzLmNsb25lTm9kZShmYWxzZSksIHBhcmVudCA9IHRoaXMucGFyZW50Tm9kZTtcbiAgcmV0dXJuIHBhcmVudCA/IHBhcmVudC5pbnNlcnRCZWZvcmUoY2xvbmUsIHRoaXMubmV4dFNpYmxpbmcpIDogY2xvbmU7XG59XG5cbmZ1bmN0aW9uIHNlbGVjdGlvbl9jbG9uZURlZXAoKSB7XG4gIHZhciBjbG9uZSA9IHRoaXMuY2xvbmVOb2RlKHRydWUpLCBwYXJlbnQgPSB0aGlzLnBhcmVudE5vZGU7XG4gIHJldHVybiBwYXJlbnQgPyBwYXJlbnQuaW5zZXJ0QmVmb3JlKGNsb25lLCB0aGlzLm5leHRTaWJsaW5nKSA6IGNsb25lO1xufVxuXG5leHBvcnQgZGVmYXVsdCBmdW5jdGlvbihkZWVwKSB7XG4gIHJldHVybiB0aGlzLnNlbGVjdChkZWVwID8gc2VsZWN0aW9uX2Nsb25lRGVlcCA6IHNlbGVjdGlvbl9jbG9uZVNoYWxsb3cpO1xufVxuIiwiZXhwb3J0IGRlZmF1bHQgZnVuY3Rpb24odmFsdWUpIHtcbiAgcmV0dXJuIGFyZ3VtZW50cy5sZW5ndGhcbiAgICAgID8gdGhpcy5wcm9wZXJ0eShcIl9fZGF0YV9fXCIsIHZhbHVlKVxuICAgICAgOiB0aGlzLm5vZGUoKS5fX2RhdGFfXztcbn1cbiIsImZ1bmN0aW9uIGNvbnRleHRMaXN0ZW5lcihsaXN0ZW5lcikge1xuICByZXR1cm4gZnVuY3Rpb24oZXZlbnQpIHtcbiAgICBsaXN0ZW5lci5jYWxsKHRoaXMsIGV2ZW50LCB0aGlzLl9fZGF0YV9fKTtcbiAgfTtcbn1cblxuZnVuY3Rpb24gcGFyc2VUeXBlbmFtZXModHlwZW5hbWVzKSB7XG4gIHJldHVybiB0eXBlbmFtZXMudHJpbSgpLnNwbGl0KC9efFxccysvKS5tYXAoZnVuY3Rpb24odCkge1xuICAgIHZhciBuYW1lID0gXCJcIiwgaSA9IHQuaW5kZXhPZihcIi5cIik7XG4gICAgaWYgKGkgPj0gMCkgbmFtZSA9IHQuc2xpY2UoaSArIDEpLCB0ID0gdC5zbGljZSgwLCBpKTtcbiAgICByZXR1cm4ge3R5cGU6IHQsIG5hbWU6IG5hbWV9O1xuICB9KTtcbn1cblxuZnVuY3Rpb24gb25SZW1vdmUodHlwZW5hbWUpIHtcbiAgcmV0dXJuIGZ1bmN0aW9uKCkge1xuICAgIHZhciBvbiA9IHRoaXMuX19vbjtcbiAgICBpZiAoIW9uKSByZXR1cm47XG4gICAgZm9yICh2YXIgaiA9IDAsIGkgPSAtMSwgbSA9IG9uLmxlbmd0aCwgbzsgaiA8IG07ICsraikge1xuICAgICAgaWYgKG8gPSBvbltqXSwgKCF0eXBlbmFtZS50eXBlIHx8IG8udHlwZSA9PT0gdHlwZW5hbWUudHlwZSkgJiYgby5uYW1lID09PSB0eXBlbmFtZS5uYW1lKSB7XG4gICAgICAgIHRoaXMucmVtb3ZlRXZlbnRMaXN0ZW5lcihvLnR5cGUsIG8ubGlzdGVuZXIsIG8ub3B0aW9ucyk7XG4gICAgICB9IGVsc2Uge1xuICAgICAgICBvblsrK2ldID0gbztcbiAgICAgIH1cbiAgICB9XG4gICAgaWYgKCsraSkgb24ubGVuZ3RoID0gaTtcbiAgICBlbHNlIGRlbGV0ZSB0aGlzLl9fb247XG4gIH07XG59XG5cbmZ1bmN0aW9uIG9uQWRkKHR5cGVuYW1lLCB2YWx1ZSwgb3B0aW9ucykge1xuICByZXR1cm4gZnVuY3Rpb24oKSB7XG4gICAgdmFyIG9uID0gdGhpcy5fX29uLCBvLCBsaXN0ZW5lciA9IGNvbnRleHRMaXN0ZW5lcih2YWx1ZSk7XG4gICAgaWYgKG9uKSBmb3IgKHZhciBqID0gMCwgbSA9IG9uLmxlbmd0aDsgaiA8IG07ICsraikge1xuICAgICAgaWYgKChvID0gb25bal0pLnR5cGUgPT09IHR5cGVuYW1lLnR5cGUgJiYgby5uYW1lID09PSB0eXBlbmFtZS5uYW1lKSB7XG4gICAgICAgIHRoaXMucmVtb3ZlRXZlbnRMaXN0ZW5lcihvLnR5cGUsIG8ubGlzdGVuZXIsIG8ub3B0aW9ucyk7XG4gICAgICAgIHRoaXMuYWRkRXZlbnRMaXN0ZW5lcihvLnR5cGUsIG8ubGlzdGVuZXIgPSBsaXN0ZW5lciwgby5vcHRpb25zID0gb3B0aW9ucyk7XG4gICAgICAgIG8udmFsdWUgPSB2YWx1ZTtcbiAgICAgICAgcmV0dXJuO1xuICAgICAgfVxuICAgIH1cbiAgICB0aGlzLmFkZEV2ZW50TGlzdGVuZXIodHlwZW5hbWUudHlwZSwgbGlzdGVuZXIsIG9wdGlvbnMpO1xuICAgIG8gPSB7dHlwZTogdHlwZW5hbWUudHlwZSwgbmFtZTogdHlwZW5hbWUubmFtZSwgdmFsdWU6IHZhbHVlLCBsaXN0ZW5lcjogbGlzdGVuZXIsIG9wdGlvbnM6IG9wdGlvbnN9O1xuICAgIGlmICghb24pIHRoaXMuX19vbiA9IFtvXTtcbiAgICBlbHNlIG9uLnB1c2gobyk7XG4gIH07XG59XG5cbmV4cG9ydCBkZWZhdWx0IGZ1bmN0aW9uKHR5cGVuYW1lLCB2YWx1ZSwgb3B0aW9ucykge1xuICB2YXIgdHlwZW5hbWVzID0gcGFyc2VUeXBlbmFtZXModHlwZW5hbWUgKyBcIlwiKSwgaSwgbiA9IHR5cGVuYW1lcy5sZW5ndGgsIHQ7XG5cbiAgaWYgKGFyZ3VtZW50cy5sZW5ndGggPCAyKSB7XG4gICAgdmFyIG9uID0gdGhpcy5ub2RlKCkuX19vbjtcbiAgICBpZiAob24pIGZvciAodmFyIGogPSAwLCBtID0gb24ubGVuZ3RoLCBvOyBqIDwgbTsgKytqKSB7XG4gICAgICBmb3IgKGkgPSAwLCBvID0gb25bal07IGkgPCBuOyArK2kpIHtcbiAgICAgICAgaWYgKCh0ID0gdHlwZW5hbWVzW2ldKS50eXBlID09PSBvLnR5cGUgJiYgdC5uYW1lID09PSBvLm5hbWUpIHtcbiAgICAgICAgICByZXR1cm4gby52YWx1ZTtcbiAgICAgICAgfVxuICAgICAgfVxuICAgIH1cbiAgICByZXR1cm47XG4gIH1cblxuICBvbiA9IHZhbHVlID8gb25BZGQgOiBvblJlbW92ZTtcbiAgZm9yIChpID0gMDsgaSA8IG47ICsraSkgdGhpcy5lYWNoKG9uKHR5cGVuYW1lc1tpXSwgdmFsdWUsIG9wdGlvbnMpKTtcbiAgcmV0dXJuIHRoaXM7XG59XG4iLCJpbXBvcnQgZGVmYXVsdFZpZXcgZnJvbSBcIi4uL3dpbmRvdy5qc1wiO1xuXG5mdW5jdGlvbiBkaXNwYXRjaEV2ZW50KG5vZGUsIHR5cGUsIHBhcmFtcykge1xuICB2YXIgd2luZG93ID0gZGVmYXVsdFZpZXcobm9kZSksXG4gICAgICBldmVudCA9IHdpbmRvdy5DdXN0b21FdmVudDtcblxuICBpZiAodHlwZW9mIGV2ZW50ID09PSBcImZ1bmN0aW9uXCIpIHtcbiAgICBldmVudCA9IG5ldyBldmVudCh0eXBlLCBwYXJhbXMpO1xuICB9IGVsc2Uge1xuICAgIGV2ZW50ID0gd2luZG93LmRvY3VtZW50LmNyZWF0ZUV2ZW50KFwiRXZlbnRcIik7XG4gICAgaWYgKHBhcmFtcykgZXZlbnQuaW5pdEV2ZW50KHR5cGUsIHBhcmFtcy5idWJibGVzLCBwYXJhbXMuY2FuY2VsYWJsZSksIGV2ZW50LmRldGFpbCA9IHBhcmFtcy5kZXRhaWw7XG4gICAgZWxzZSBldmVudC5pbml0RXZlbnQodHlwZSwgZmFsc2UsIGZhbHNlKTtcbiAgfVxuXG4gIG5vZGUuZGlzcGF0Y2hFdmVudChldmVudCk7XG59XG5cbmZ1bmN0aW9uIGRpc3BhdGNoQ29uc3RhbnQodHlwZSwgcGFyYW1zKSB7XG4gIHJldHVybiBmdW5jdGlvbigpIHtcbiAgICByZXR1cm4gZGlzcGF0Y2hFdmVudCh0aGlzLCB0eXBlLCBwYXJhbXMpO1xuICB9O1xufVxuXG5mdW5jdGlvbiBkaXNwYXRjaEZ1bmN0aW9uKHR5cGUsIHBhcmFtcykge1xuICByZXR1cm4gZnVuY3Rpb24oKSB7XG4gICAgcmV0dXJuIGRpc3BhdGNoRXZlbnQodGhpcywgdHlwZSwgcGFyYW1zLmFwcGx5KHRoaXMsIGFyZ3VtZW50cykpO1xuICB9O1xufVxuXG5leHBvcnQgZGVmYXVsdCBmdW5jdGlvbih0eXBlLCBwYXJhbXMpIHtcbiAgcmV0dXJuIHRoaXMuZWFjaCgodHlwZW9mIHBhcmFtcyA9PT0gXCJmdW5jdGlvblwiXG4gICAgICA/IGRpc3BhdGNoRnVuY3Rpb25cbiAgICAgIDogZGlzcGF0Y2hDb25zdGFudCkodHlwZSwgcGFyYW1zKSk7XG59XG4iLCJleHBvcnQgZGVmYXVsdCBmdW5jdGlvbiooKSB7XG4gIGZvciAodmFyIGdyb3VwcyA9IHRoaXMuX2dyb3VwcywgaiA9IDAsIG0gPSBncm91cHMubGVuZ3RoOyBqIDwgbTsgKytqKSB7XG4gICAgZm9yICh2YXIgZ3JvdXAgPSBncm91cHNbal0sIGkgPSAwLCBuID0gZ3JvdXAubGVuZ3RoLCBub2RlOyBpIDwgbjsgKytpKSB7XG4gICAgICBpZiAobm9kZSA9IGdyb3VwW2ldKSB5aWVsZCBub2RlO1xuICAgIH1cbiAgfVxufVxuIiwiaW1wb3J0IHNlbGVjdGlvbl9zZWxlY3QgZnJvbSBcIi4vc2VsZWN0LmpzXCI7XG5pbXBvcnQgc2VsZWN0aW9uX3NlbGVjdEFsbCBmcm9tIFwiLi9zZWxlY3RBbGwuanNcIjtcbmltcG9ydCBzZWxlY3Rpb25fc2VsZWN0Q2hpbGQgZnJvbSBcIi4vc2VsZWN0Q2hpbGQuanNcIjtcbmltcG9ydCBzZWxlY3Rpb25fc2VsZWN0Q2hpbGRyZW4gZnJvbSBcIi4vc2VsZWN0Q2hpbGRyZW4uanNcIjtcbmltcG9ydCBzZWxlY3Rpb25fZmlsdGVyIGZyb20gXCIuL2ZpbHRlci5qc1wiO1xuaW1wb3J0IHNlbGVjdGlvbl9kYXRhIGZyb20gXCIuL2RhdGEuanNcIjtcbmltcG9ydCBzZWxlY3Rpb25fZW50ZXIgZnJvbSBcIi4vZW50ZXIuanNcIjtcbmltcG9ydCBzZWxlY3Rpb25fZXhpdCBmcm9tIFwiLi9leGl0LmpzXCI7XG5pbXBvcnQgc2VsZWN0aW9uX2pvaW4gZnJvbSBcIi4vam9pbi5qc1wiO1xuaW1wb3J0IHNlbGVjdGlvbl9tZXJnZSBmcm9tIFwiLi9tZXJnZS5qc1wiO1xuaW1wb3J0IHNlbGVjdGlvbl9vcmRlciBmcm9tIFwiLi9vcmRlci5qc1wiO1xuaW1wb3J0IHNlbGVjdGlvbl9zb3J0IGZyb20gXCIuL3NvcnQuanNcIjtcbmltcG9ydCBzZWxlY3Rpb25fY2FsbCBmcm9tIFwiLi9jYWxsLmpzXCI7XG5pbXBvcnQgc2VsZWN0aW9uX25vZGVzIGZyb20gXCIuL25vZGVzLmpzXCI7XG5pbXBvcnQgc2VsZWN0aW9uX25vZGUgZnJvbSBcIi4vbm9kZS5qc1wiO1xuaW1wb3J0IHNlbGVjdGlvbl9zaXplIGZyb20gXCIuL3NpemUuanNcIjtcbmltcG9ydCBzZWxlY3Rpb25fZW1wdHkgZnJvbSBcIi4vZW1wdHkuanNcIjtcbmltcG9ydCBzZWxlY3Rpb25fZWFjaCBmcm9tIFwiLi9lYWNoLmpzXCI7XG5pbXBvcnQgc2VsZWN0aW9uX2F0dHIgZnJvbSBcIi4vYXR0ci5qc1wiO1xuaW1wb3J0IHNlbGVjdGlvbl9zdHlsZSBmcm9tIFwiLi9zdHlsZS5qc1wiO1xuaW1wb3J0IHNlbGVjdGlvbl9wcm9wZXJ0eSBmcm9tIFwiLi9wcm9wZXJ0eS5qc1wiO1xuaW1wb3J0IHNlbGVjdGlvbl9jbGFzc2VkIGZyb20gXCIuL2NsYXNzZWQuanNcIjtcbmltcG9ydCBzZWxlY3Rpb25fdGV4dCBmcm9tIFwiLi90ZXh0LmpzXCI7XG5pbXBvcnQgc2VsZWN0aW9uX2h0bWwgZnJvbSBcIi4vaHRtbC5qc1wiO1xuaW1wb3J0IHNlbGVjdGlvbl9yYWlzZSBmcm9tIFwiLi9yYWlzZS5qc1wiO1xuaW1wb3J0IHNlbGVjdGlvbl9sb3dlciBmcm9tIFwiLi9sb3dlci5qc1wiO1xuaW1wb3J0IHNlbGVjdGlvbl9hcHBlbmQgZnJvbSBcIi4vYXBwZW5kLmpzXCI7XG5pbXBvcnQgc2VsZWN0aW9uX2luc2VydCBmcm9tIFwiLi9pbnNlcnQuanNcIjtcbmltcG9ydCBzZWxlY3Rpb25fcmVtb3ZlIGZyb20gXCIuL3JlbW92ZS5qc1wiO1xuaW1wb3J0IHNlbGVjdGlvbl9jbG9uZSBmcm9tIFwiLi9jbG9uZS5qc1wiO1xuaW1wb3J0IHNlbGVjdGlvbl9kYXR1bSBmcm9tIFwiLi9kYXR1bS5qc1wiO1xuaW1wb3J0IHNlbGVjdGlvbl9vbiBmcm9tIFwiLi9vbi5qc1wiO1xuaW1wb3J0IHNlbGVjdGlvbl9kaXNwYXRjaCBmcm9tIFwiLi9kaXNwYXRjaC5qc1wiO1xuaW1wb3J0IHNlbGVjdGlvbl9pdGVyYXRvciBmcm9tIFwiLi9pdGVyYXRvci5qc1wiO1xuXG5leHBvcnQgdmFyIHJvb3QgPSBbbnVsbF07XG5cbmV4cG9ydCBmdW5jdGlvbiBTZWxlY3Rpb24oZ3JvdXBzLCBwYXJlbnRzKSB7XG4gIHRoaXMuX2dyb3VwcyA9IGdyb3VwcztcbiAgdGhpcy5fcGFyZW50cyA9IHBhcmVudHM7XG59XG5cbmZ1bmN0aW9uIHNlbGVjdGlvbigpIHtcbiAgcmV0dXJuIG5ldyBTZWxlY3Rpb24oW1tkb2N1bWVudC5kb2N1bWVudEVsZW1lbnRdXSwgcm9vdCk7XG59XG5cbmZ1bmN0aW9uIHNlbGVjdGlvbl9zZWxlY3Rpb24oKSB7XG4gIHJldHVybiB0aGlzO1xufVxuXG5TZWxlY3Rpb24ucHJvdG90eXBlID0gc2VsZWN0aW9uLnByb3RvdHlwZSA9IHtcbiAgY29uc3RydWN0b3I6IFNlbGVjdGlvbixcbiAgc2VsZWN0OiBzZWxlY3Rpb25fc2VsZWN0LFxuICBzZWxlY3RBbGw6IHNlbGVjdGlvbl9zZWxlY3RBbGwsXG4gIHNlbGVjdENoaWxkOiBzZWxlY3Rpb25fc2VsZWN0Q2hpbGQsXG4gIHNlbGVjdENoaWxkcmVuOiBzZWxlY3Rpb25fc2VsZWN0Q2hpbGRyZW4sXG4gIGZpbHRlcjogc2VsZWN0aW9uX2ZpbHRlcixcbiAgZGF0YTogc2VsZWN0aW9uX2RhdGEsXG4gIGVudGVyOiBzZWxlY3Rpb25fZW50ZXIsXG4gIGV4aXQ6IHNlbGVjdGlvbl9leGl0LFxuICBqb2luOiBzZWxlY3Rpb25fam9pbixcbiAgbWVyZ2U6IHNlbGVjdGlvbl9tZXJnZSxcbiAgc2VsZWN0aW9uOiBzZWxlY3Rpb25fc2VsZWN0aW9uLFxuICBvcmRlcjogc2VsZWN0aW9uX29yZGVyLFxuICBzb3J0OiBzZWxlY3Rpb25fc29ydCxcbiAgY2FsbDogc2VsZWN0aW9uX2NhbGwsXG4gIG5vZGVzOiBzZWxlY3Rpb25fbm9kZXMsXG4gIG5vZGU6IHNlbGVjdGlvbl9ub2RlLFxuICBzaXplOiBzZWxlY3Rpb25fc2l6ZSxcbiAgZW1wdHk6IHNlbGVjdGlvbl9lbXB0eSxcbiAgZWFjaDogc2VsZWN0aW9uX2VhY2gsXG4gIGF0dHI6IHNlbGVjdGlvbl9hdHRyLFxuICBzdHlsZTogc2VsZWN0aW9uX3N0eWxlLFxuICBwcm9wZXJ0eTogc2VsZWN0aW9uX3Byb3BlcnR5LFxuICBjbGFzc2VkOiBzZWxlY3Rpb25fY2xhc3NlZCxcbiAgdGV4dDogc2VsZWN0aW9uX3RleHQsXG4gIGh0bWw6IHNlbGVjdGlvbl9odG1sLFxuICByYWlzZTogc2VsZWN0aW9uX3JhaXNlLFxuICBsb3dlcjogc2VsZWN0aW9uX2xvd2VyLFxuICBhcHBlbmQ6IHNlbGVjdGlvbl9hcHBlbmQsXG4gIGluc2VydDogc2VsZWN0aW9uX2luc2VydCxcbiAgcmVtb3ZlOiBzZWxlY3Rpb25fcmVtb3ZlLFxuICBjbG9uZTogc2VsZWN0aW9uX2Nsb25lLFxuICBkYXR1bTogc2VsZWN0aW9uX2RhdHVtLFxuICBvbjogc2VsZWN0aW9uX29uLFxuICBkaXNwYXRjaDogc2VsZWN0aW9uX2Rpc3BhdGNoLFxuICBbU3ltYm9sLml0ZXJhdG9yXTogc2VsZWN0aW9uX2l0ZXJhdG9yXG59O1xuXG5leHBvcnQgZGVmYXVsdCBzZWxlY3Rpb247XG4iLCJpbXBvcnQge1NlbGVjdGlvbiwgcm9vdH0gZnJvbSBcIi4vc2VsZWN0aW9uL2luZGV4LmpzXCI7XG5cbmV4cG9ydCBkZWZhdWx0IGZ1bmN0aW9uKHNlbGVjdG9yKSB7XG4gIHJldHVybiB0eXBlb2Ygc2VsZWN0b3IgPT09IFwic3RyaW5nXCJcbiAgICAgID8gbmV3IFNlbGVjdGlvbihbW2RvY3VtZW50LnF1ZXJ5U2VsZWN0b3Ioc2VsZWN0b3IpXV0sIFtkb2N1bWVudC5kb2N1bWVudEVsZW1lbnRdKVxuICAgICAgOiBuZXcgU2VsZWN0aW9uKFtbc2VsZWN0b3JdXSwgcm9vdCk7XG59XG4iLCJleHBvcnQgZGVmYXVsdCBmdW5jdGlvbihldmVudCkge1xuICBsZXQgc291cmNlRXZlbnQ7XG4gIHdoaWxlIChzb3VyY2VFdmVudCA9IGV2ZW50LnNvdXJjZUV2ZW50KSBldmVudCA9IHNvdXJjZUV2ZW50O1xuICByZXR1cm4gZXZlbnQ7XG59XG4iLCJpbXBvcnQgc291cmNlRXZlbnQgZnJvbSBcIi4vc291cmNlRXZlbnQuanNcIjtcblxuZXhwb3J0IGRlZmF1bHQgZnVuY3Rpb24oZXZlbnQsIG5vZGUpIHtcbiAgZXZlbnQgPSBzb3VyY2VFdmVudChldmVudCk7XG4gIGlmIChub2RlID09PSB1bmRlZmluZWQpIG5vZGUgPSBldmVudC5jdXJyZW50VGFyZ2V0O1xuICBpZiAobm9kZSkge1xuICAgIHZhciBzdmcgPSBub2RlLm93bmVyU1ZHRWxlbWVudCB8fCBub2RlO1xuICAgIGlmIChzdmcuY3JlYXRlU1ZHUG9pbnQpIHtcbiAgICAgIHZhciBwb2ludCA9IHN2Zy5jcmVhdGVTVkdQb2ludCgpO1xuICAgICAgcG9pbnQueCA9IGV2ZW50LmNsaWVudFgsIHBvaW50LnkgPSBldmVudC5jbGllbnRZO1xuICAgICAgcG9pbnQgPSBwb2ludC5tYXRyaXhUcmFuc2Zvcm0obm9kZS5nZXRTY3JlZW5DVE0oKS5pbnZlcnNlKCkpO1xuICAgICAgcmV0dXJuIFtwb2ludC54LCBwb2ludC55XTtcbiAgICB9XG4gICAgaWYgKG5vZGUuZ2V0Qm91bmRpbmdDbGllbnRSZWN0KSB7XG4gICAgICB2YXIgcmVjdCA9IG5vZGUuZ2V0Qm91bmRpbmdDbGllbnRSZWN0KCk7XG4gICAgICByZXR1cm4gW2V2ZW50LmNsaWVudFggLSByZWN0LmxlZnQgLSBub2RlLmNsaWVudExlZnQsIGV2ZW50LmNsaWVudFkgLSByZWN0LnRvcCAtIG5vZGUuY2xpZW50VG9wXTtcbiAgICB9XG4gIH1cbiAgcmV0dXJuIFtldmVudC5wYWdlWCwgZXZlbnQucGFnZVldO1xufVxuIiwidmFyIG5vb3AgPSB7dmFsdWU6ICgpID0+IHt9fTtcblxuZnVuY3Rpb24gZGlzcGF0Y2goKSB7XG4gIGZvciAodmFyIGkgPSAwLCBuID0gYXJndW1lbnRzLmxlbmd0aCwgXyA9IHt9LCB0OyBpIDwgbjsgKytpKSB7XG4gICAgaWYgKCEodCA9IGFyZ3VtZW50c1tpXSArIFwiXCIpIHx8ICh0IGluIF8pIHx8IC9bXFxzLl0vLnRlc3QodCkpIHRocm93IG5ldyBFcnJvcihcImlsbGVnYWwgdHlwZTogXCIgKyB0KTtcbiAgICBfW3RdID0gW107XG4gIH1cbiAgcmV0dXJuIG5ldyBEaXNwYXRjaChfKTtcbn1cblxuZnVuY3Rpb24gRGlzcGF0Y2goXykge1xuICB0aGlzLl8gPSBfO1xufVxuXG5mdW5jdGlvbiBwYXJzZVR5cGVuYW1lcyh0eXBlbmFtZXMsIHR5cGVzKSB7XG4gIHJldHVybiB0eXBlbmFtZXMudHJpbSgpLnNwbGl0KC9efFxccysvKS5tYXAoZnVuY3Rpb24odCkge1xuICAgIHZhciBuYW1lID0gXCJcIiwgaSA9IHQuaW5kZXhPZihcIi5cIik7XG4gICAgaWYgKGkgPj0gMCkgbmFtZSA9IHQuc2xpY2UoaSArIDEpLCB0ID0gdC5zbGljZSgwLCBpKTtcbiAgICBpZiAodCAmJiAhdHlwZXMuaGFzT3duUHJvcGVydHkodCkpIHRocm93IG5ldyBFcnJvcihcInVua25vd24gdHlwZTogXCIgKyB0KTtcbiAgICByZXR1cm4ge3R5cGU6IHQsIG5hbWU6IG5hbWV9O1xuICB9KTtcbn1cblxuRGlzcGF0Y2gucHJvdG90eXBlID0gZGlzcGF0Y2gucHJvdG90eXBlID0ge1xuICBjb25zdHJ1Y3RvcjogRGlzcGF0Y2gsXG4gIG9uOiBmdW5jdGlvbih0eXBlbmFtZSwgY2FsbGJhY2spIHtcbiAgICB2YXIgXyA9IHRoaXMuXyxcbiAgICAgICAgVCA9IHBhcnNlVHlwZW5hbWVzKHR5cGVuYW1lICsgXCJcIiwgXyksXG4gICAgICAgIHQsXG4gICAgICAgIGkgPSAtMSxcbiAgICAgICAgbiA9IFQubGVuZ3RoO1xuXG4gICAgLy8gSWYgbm8gY2FsbGJhY2sgd2FzIHNwZWNpZmllZCwgcmV0dXJuIHRoZSBjYWxsYmFjayBvZiB0aGUgZ2l2ZW4gdHlwZSBhbmQgbmFtZS5cbiAgICBpZiAoYXJndW1lbnRzLmxlbmd0aCA8IDIpIHtcbiAgICAgIHdoaWxlICgrK2kgPCBuKSBpZiAoKHQgPSAodHlwZW5hbWUgPSBUW2ldKS50eXBlKSAmJiAodCA9IGdldChfW3RdLCB0eXBlbmFtZS5uYW1lKSkpIHJldHVybiB0O1xuICAgICAgcmV0dXJuO1xuICAgIH1cblxuICAgIC8vIElmIGEgdHlwZSB3YXMgc3BlY2lmaWVkLCBzZXQgdGhlIGNhbGxiYWNrIGZvciB0aGUgZ2l2ZW4gdHlwZSBhbmQgbmFtZS5cbiAgICAvLyBPdGhlcndpc2UsIGlmIGEgbnVsbCBjYWxsYmFjayB3YXMgc3BlY2lmaWVkLCByZW1vdmUgY2FsbGJhY2tzIG9mIHRoZSBnaXZlbiBuYW1lLlxuICAgIGlmIChjYWxsYmFjayAhPSBudWxsICYmIHR5cGVvZiBjYWxsYmFjayAhPT0gXCJmdW5jdGlvblwiKSB0aHJvdyBuZXcgRXJyb3IoXCJpbnZhbGlkIGNhbGxiYWNrOiBcIiArIGNhbGxiYWNrKTtcbiAgICB3aGlsZSAoKytpIDwgbikge1xuICAgICAgaWYgKHQgPSAodHlwZW5hbWUgPSBUW2ldKS50eXBlKSBfW3RdID0gc2V0KF9bdF0sIHR5cGVuYW1lLm5hbWUsIGNhbGxiYWNrKTtcbiAgICAgIGVsc2UgaWYgKGNhbGxiYWNrID09IG51bGwpIGZvciAodCBpbiBfKSBfW3RdID0gc2V0KF9bdF0sIHR5cGVuYW1lLm5hbWUsIG51bGwpO1xuICAgIH1cblxuICAgIHJldHVybiB0aGlzO1xuICB9LFxuICBjb3B5OiBmdW5jdGlvbigpIHtcbiAgICB2YXIgY29weSA9IHt9LCBfID0gdGhpcy5fO1xuICAgIGZvciAodmFyIHQgaW4gXykgY29weVt0XSA9IF9bdF0uc2xpY2UoKTtcbiAgICByZXR1cm4gbmV3IERpc3BhdGNoKGNvcHkpO1xuICB9LFxuICBjYWxsOiBmdW5jdGlvbih0eXBlLCB0aGF0KSB7XG4gICAgaWYgKChuID0gYXJndW1lbnRzLmxlbmd0aCAtIDIpID4gMCkgZm9yICh2YXIgYXJncyA9IG5ldyBBcnJheShuKSwgaSA9IDAsIG4sIHQ7IGkgPCBuOyArK2kpIGFyZ3NbaV0gPSBhcmd1bWVudHNbaSArIDJdO1xuICAgIGlmICghdGhpcy5fLmhhc093blByb3BlcnR5KHR5cGUpKSB0aHJvdyBuZXcgRXJyb3IoXCJ1bmtub3duIHR5cGU6IFwiICsgdHlwZSk7XG4gICAgZm9yICh0ID0gdGhpcy5fW3R5cGVdLCBpID0gMCwgbiA9IHQubGVuZ3RoOyBpIDwgbjsgKytpKSB0W2ldLnZhbHVlLmFwcGx5KHRoYXQsIGFyZ3MpO1xuICB9LFxuICBhcHBseTogZnVuY3Rpb24odHlwZSwgdGhhdCwgYXJncykge1xuICAgIGlmICghdGhpcy5fLmhhc093blByb3BlcnR5KHR5cGUpKSB0aHJvdyBuZXcgRXJyb3IoXCJ1bmtub3duIHR5cGU6IFwiICsgdHlwZSk7XG4gICAgZm9yICh2YXIgdCA9IHRoaXMuX1t0eXBlXSwgaSA9IDAsIG4gPSB0Lmxlbmd0aDsgaSA8IG47ICsraSkgdFtpXS52YWx1ZS5hcHBseSh0aGF0LCBhcmdzKTtcbiAgfVxufTtcblxuZnVuY3Rpb24gZ2V0KHR5cGUsIG5hbWUpIHtcbiAgZm9yICh2YXIgaSA9IDAsIG4gPSB0eXBlLmxlbmd0aCwgYzsgaSA8IG47ICsraSkge1xuICAgIGlmICgoYyA9IHR5cGVbaV0pLm5hbWUgPT09IG5hbWUpIHtcbiAgICAgIHJldHVybiBjLnZhbHVlO1xuICAgIH1cbiAgfVxufVxuXG5mdW5jdGlvbiBzZXQodHlwZSwgbmFtZSwgY2FsbGJhY2spIHtcbiAgZm9yICh2YXIgaSA9IDAsIG4gPSB0eXBlLmxlbmd0aDsgaSA8IG47ICsraSkge1xuICAgIGlmICh0eXBlW2ldLm5hbWUgPT09IG5hbWUpIHtcbiAgICAgIHR5cGVbaV0gPSBub29wLCB0eXBlID0gdHlwZS5zbGljZSgwLCBpKS5jb25jYXQodHlwZS5zbGljZShpICsgMSkpO1xuICAgICAgYnJlYWs7XG4gICAgfVxuICB9XG4gIGlmIChjYWxsYmFjayAhPSBudWxsKSB0eXBlLnB1c2goe25hbWU6IG5hbWUsIHZhbHVlOiBjYWxsYmFja30pO1xuICByZXR1cm4gdHlwZTtcbn1cblxuZXhwb3J0IGRlZmF1bHQgZGlzcGF0Y2g7XG4iLCIvLyBUaGVzZSBhcmUgdHlwaWNhbGx5IHVzZWQgaW4gY29uanVuY3Rpb24gd2l0aCBub2V2ZW50IHRvIGVuc3VyZSB0aGF0IHdlIGNhblxuLy8gcHJldmVudERlZmF1bHQgb24gdGhlIGV2ZW50LlxuZXhwb3J0IGNvbnN0IG5vbnBhc3NpdmUgPSB7cGFzc2l2ZTogZmFsc2V9O1xuZXhwb3J0IGNvbnN0IG5vbnBhc3NpdmVjYXB0dXJlID0ge2NhcHR1cmU6IHRydWUsIHBhc3NpdmU6IGZhbHNlfTtcblxuZXhwb3J0IGZ1bmN0aW9uIG5vcHJvcGFnYXRpb24oZXZlbnQpIHtcbiAgZXZlbnQuc3RvcEltbWVkaWF0ZVByb3BhZ2F0aW9uKCk7XG59XG5cbmV4cG9ydCBkZWZhdWx0IGZ1bmN0aW9uKGV2ZW50KSB7XG4gIGV2ZW50LnByZXZlbnREZWZhdWx0KCk7XG4gIGV2ZW50LnN0b3BJbW1lZGlhdGVQcm9wYWdhdGlvbigpO1xufVxuIiwiaW1wb3J0IHtzZWxlY3R9IGZyb20gXCJkMy1zZWxlY3Rpb25cIjtcbmltcG9ydCBub2V2ZW50LCB7bm9ucGFzc2l2ZWNhcHR1cmV9IGZyb20gXCIuL25vZXZlbnQuanNcIjtcblxuZXhwb3J0IGRlZmF1bHQgZnVuY3Rpb24odmlldykge1xuICB2YXIgcm9vdCA9IHZpZXcuZG9jdW1lbnQuZG9jdW1lbnRFbGVtZW50LFxuICAgICAgc2VsZWN0aW9uID0gc2VsZWN0KHZpZXcpLm9uKFwiZHJhZ3N0YXJ0LmRyYWdcIiwgbm9ldmVudCwgbm9ucGFzc2l2ZWNhcHR1cmUpO1xuICBpZiAoXCJvbnNlbGVjdHN0YXJ0XCIgaW4gcm9vdCkge1xuICAgIHNlbGVjdGlvbi5vbihcInNlbGVjdHN0YXJ0LmRyYWdcIiwgbm9ldmVudCwgbm9ucGFzc2l2ZWNhcHR1cmUpO1xuICB9IGVsc2Uge1xuICAgIHJvb3QuX19ub3NlbGVjdCA9IHJvb3Quc3R5bGUuTW96VXNlclNlbGVjdDtcbiAgICByb290LnN0eWxlLk1velVzZXJTZWxlY3QgPSBcIm5vbmVcIjtcbiAgfVxufVxuXG5leHBvcnQgZnVuY3Rpb24geWVzZHJhZyh2aWV3LCBub2NsaWNrKSB7XG4gIHZhciByb290ID0gdmlldy5kb2N1bWVudC5kb2N1bWVudEVsZW1lbnQsXG4gICAgICBzZWxlY3Rpb24gPSBzZWxlY3Qodmlldykub24oXCJkcmFnc3RhcnQuZHJhZ1wiLCBudWxsKTtcbiAgaWYgKG5vY2xpY2spIHtcbiAgICBzZWxlY3Rpb24ub24oXCJjbGljay5kcmFnXCIsIG5vZXZlbnQsIG5vbnBhc3NpdmVjYXB0dXJlKTtcbiAgICBzZXRUaW1lb3V0KGZ1bmN0aW9uKCkgeyBzZWxlY3Rpb24ub24oXCJjbGljay5kcmFnXCIsIG51bGwpOyB9LCAwKTtcbiAgfVxuICBpZiAoXCJvbnNlbGVjdHN0YXJ0XCIgaW4gcm9vdCkge1xuICAgIHNlbGVjdGlvbi5vbihcInNlbGVjdHN0YXJ0LmRyYWdcIiwgbnVsbCk7XG4gIH0gZWxzZSB7XG4gICAgcm9vdC5zdHlsZS5Nb3pVc2VyU2VsZWN0ID0gcm9vdC5fX25vc2VsZWN0O1xuICAgIGRlbGV0ZSByb290Ll9fbm9zZWxlY3Q7XG4gIH1cbn1cbiIsImV4cG9ydCBkZWZhdWx0IGZ1bmN0aW9uKGNvbnN0cnVjdG9yLCBmYWN0b3J5LCBwcm90b3R5cGUpIHtcbiAgY29uc3RydWN0b3IucHJvdG90eXBlID0gZmFjdG9yeS5wcm90b3R5cGUgPSBwcm90b3R5cGU7XG4gIHByb3RvdHlwZS5jb25zdHJ1Y3RvciA9IGNvbnN0cnVjdG9yO1xufVxuXG5leHBvcnQgZnVuY3Rpb24gZXh0ZW5kKHBhcmVudCwgZGVmaW5pdGlvbikge1xuICB2YXIgcHJvdG90eXBlID0gT2JqZWN0LmNyZWF0ZShwYXJlbnQucHJvdG90eXBlKTtcbiAgZm9yICh2YXIga2V5IGluIGRlZmluaXRpb24pIHByb3RvdHlwZVtrZXldID0gZGVmaW5pdGlvbltrZXldO1xuICByZXR1cm4gcHJvdG90eXBlO1xufVxuIiwiaW1wb3J0IGRlZmluZSwge2V4dGVuZH0gZnJvbSBcIi4vZGVmaW5lLmpzXCI7XG5cbmV4cG9ydCBmdW5jdGlvbiBDb2xvcigpIHt9XG5cbmV4cG9ydCB2YXIgZGFya2VyID0gMC43O1xuZXhwb3J0IHZhciBicmlnaHRlciA9IDEgLyBkYXJrZXI7XG5cbnZhciByZUkgPSBcIlxcXFxzKihbKy1dP1xcXFxkKylcXFxccypcIixcbiAgICByZU4gPSBcIlxcXFxzKihbKy1dPyg/OlxcXFxkKlxcXFwuKT9cXFxcZCsoPzpbZUVdWystXT9cXFxcZCspPylcXFxccypcIixcbiAgICByZVAgPSBcIlxcXFxzKihbKy1dPyg/OlxcXFxkKlxcXFwuKT9cXFxcZCsoPzpbZUVdWystXT9cXFxcZCspPyklXFxcXHMqXCIsXG4gICAgcmVIZXggPSAvXiMoWzAtOWEtZl17Myw4fSkkLyxcbiAgICByZVJnYkludGVnZXIgPSBuZXcgUmVnRXhwKGBecmdiXFxcXCgke3JlSX0sJHtyZUl9LCR7cmVJfVxcXFwpJGApLFxuICAgIHJlUmdiUGVyY2VudCA9IG5ldyBSZWdFeHAoYF5yZ2JcXFxcKCR7cmVQfSwke3JlUH0sJHtyZVB9XFxcXCkkYCksXG4gICAgcmVSZ2JhSW50ZWdlciA9IG5ldyBSZWdFeHAoYF5yZ2JhXFxcXCgke3JlSX0sJHtyZUl9LCR7cmVJfSwke3JlTn1cXFxcKSRgKSxcbiAgICByZVJnYmFQZXJjZW50ID0gbmV3IFJlZ0V4cChgXnJnYmFcXFxcKCR7cmVQfSwke3JlUH0sJHtyZVB9LCR7cmVOfVxcXFwpJGApLFxuICAgIHJlSHNsUGVyY2VudCA9IG5ldyBSZWdFeHAoYF5oc2xcXFxcKCR7cmVOfSwke3JlUH0sJHtyZVB9XFxcXCkkYCksXG4gICAgcmVIc2xhUGVyY2VudCA9IG5ldyBSZWdFeHAoYF5oc2xhXFxcXCgke3JlTn0sJHtyZVB9LCR7cmVQfSwke3JlTn1cXFxcKSRgKTtcblxudmFyIG5hbWVkID0ge1xuICBhbGljZWJsdWU6IDB4ZjBmOGZmLFxuICBhbnRpcXVld2hpdGU6IDB4ZmFlYmQ3LFxuICBhcXVhOiAweDAwZmZmZixcbiAgYXF1YW1hcmluZTogMHg3ZmZmZDQsXG4gIGF6dXJlOiAweGYwZmZmZixcbiAgYmVpZ2U6IDB4ZjVmNWRjLFxuICBiaXNxdWU6IDB4ZmZlNGM0LFxuICBibGFjazogMHgwMDAwMDAsXG4gIGJsYW5jaGVkYWxtb25kOiAweGZmZWJjZCxcbiAgYmx1ZTogMHgwMDAwZmYsXG4gIGJsdWV2aW9sZXQ6IDB4OGEyYmUyLFxuICBicm93bjogMHhhNTJhMmEsXG4gIGJ1cmx5d29vZDogMHhkZWI4ODcsXG4gIGNhZGV0Ymx1ZTogMHg1ZjllYTAsXG4gIGNoYXJ0cmV1c2U6IDB4N2ZmZjAwLFxuICBjaG9jb2xhdGU6IDB4ZDI2OTFlLFxuICBjb3JhbDogMHhmZjdmNTAsXG4gIGNvcm5mbG93ZXJibHVlOiAweDY0OTVlZCxcbiAgY29ybnNpbGs6IDB4ZmZmOGRjLFxuICBjcmltc29uOiAweGRjMTQzYyxcbiAgY3lhbjogMHgwMGZmZmYsXG4gIGRhcmtibHVlOiAweDAwMDA4YixcbiAgZGFya2N5YW46IDB4MDA4YjhiLFxuICBkYXJrZ29sZGVucm9kOiAweGI4ODYwYixcbiAgZGFya2dyYXk6IDB4YTlhOWE5LFxuICBkYXJrZ3JlZW46IDB4MDA2NDAwLFxuICBkYXJrZ3JleTogMHhhOWE5YTksXG4gIGRhcmtraGFraTogMHhiZGI3NmIsXG4gIGRhcmttYWdlbnRhOiAweDhiMDA4YixcbiAgZGFya29saXZlZ3JlZW46IDB4NTU2YjJmLFxuICBkYXJrb3JhbmdlOiAweGZmOGMwMCxcbiAgZGFya29yY2hpZDogMHg5OTMyY2MsXG4gIGRhcmtyZWQ6IDB4OGIwMDAwLFxuICBkYXJrc2FsbW9uOiAweGU5OTY3YSxcbiAgZGFya3NlYWdyZWVuOiAweDhmYmM4ZixcbiAgZGFya3NsYXRlYmx1ZTogMHg0ODNkOGIsXG4gIGRhcmtzbGF0ZWdyYXk6IDB4MmY0ZjRmLFxuICBkYXJrc2xhdGVncmV5OiAweDJmNGY0ZixcbiAgZGFya3R1cnF1b2lzZTogMHgwMGNlZDEsXG4gIGRhcmt2aW9sZXQ6IDB4OTQwMGQzLFxuICBkZWVwcGluazogMHhmZjE0OTMsXG4gIGRlZXBza3libHVlOiAweDAwYmZmZixcbiAgZGltZ3JheTogMHg2OTY5NjksXG4gIGRpbWdyZXk6IDB4Njk2OTY5LFxuICBkb2RnZXJibHVlOiAweDFlOTBmZixcbiAgZmlyZWJyaWNrOiAweGIyMjIyMixcbiAgZmxvcmFsd2hpdGU6IDB4ZmZmYWYwLFxuICBmb3Jlc3RncmVlbjogMHgyMjhiMjIsXG4gIGZ1Y2hzaWE6IDB4ZmYwMGZmLFxuICBnYWluc2Jvcm86IDB4ZGNkY2RjLFxuICBnaG9zdHdoaXRlOiAweGY4ZjhmZixcbiAgZ29sZDogMHhmZmQ3MDAsXG4gIGdvbGRlbnJvZDogMHhkYWE1MjAsXG4gIGdyYXk6IDB4ODA4MDgwLFxuICBncmVlbjogMHgwMDgwMDAsXG4gIGdyZWVueWVsbG93OiAweGFkZmYyZixcbiAgZ3JleTogMHg4MDgwODAsXG4gIGhvbmV5ZGV3OiAweGYwZmZmMCxcbiAgaG90cGluazogMHhmZjY5YjQsXG4gIGluZGlhbnJlZDogMHhjZDVjNWMsXG4gIGluZGlnbzogMHg0YjAwODIsXG4gIGl2b3J5OiAweGZmZmZmMCxcbiAga2hha2k6IDB4ZjBlNjhjLFxuICBsYXZlbmRlcjogMHhlNmU2ZmEsXG4gIGxhdmVuZGVyYmx1c2g6IDB4ZmZmMGY1LFxuICBsYXduZ3JlZW46IDB4N2NmYzAwLFxuICBsZW1vbmNoaWZmb246IDB4ZmZmYWNkLFxuICBsaWdodGJsdWU6IDB4YWRkOGU2LFxuICBsaWdodGNvcmFsOiAweGYwODA4MCxcbiAgbGlnaHRjeWFuOiAweGUwZmZmZixcbiAgbGlnaHRnb2xkZW5yb2R5ZWxsb3c6IDB4ZmFmYWQyLFxuICBsaWdodGdyYXk6IDB4ZDNkM2QzLFxuICBsaWdodGdyZWVuOiAweDkwZWU5MCxcbiAgbGlnaHRncmV5OiAweGQzZDNkMyxcbiAgbGlnaHRwaW5rOiAweGZmYjZjMSxcbiAgbGlnaHRzYWxtb246IDB4ZmZhMDdhLFxuICBsaWdodHNlYWdyZWVuOiAweDIwYjJhYSxcbiAgbGlnaHRza3libHVlOiAweDg3Y2VmYSxcbiAgbGlnaHRzbGF0ZWdyYXk6IDB4Nzc4ODk5LFxuICBsaWdodHNsYXRlZ3JleTogMHg3Nzg4OTksXG4gIGxpZ2h0c3RlZWxibHVlOiAweGIwYzRkZSxcbiAgbGlnaHR5ZWxsb3c6IDB4ZmZmZmUwLFxuICBsaW1lOiAweDAwZmYwMCxcbiAgbGltZWdyZWVuOiAweDMyY2QzMixcbiAgbGluZW46IDB4ZmFmMGU2LFxuICBtYWdlbnRhOiAweGZmMDBmZixcbiAgbWFyb29uOiAweDgwMDAwMCxcbiAgbWVkaXVtYXF1YW1hcmluZTogMHg2NmNkYWEsXG4gIG1lZGl1bWJsdWU6IDB4MDAwMGNkLFxuICBtZWRpdW1vcmNoaWQ6IDB4YmE1NWQzLFxuICBtZWRpdW1wdXJwbGU6IDB4OTM3MGRiLFxuICBtZWRpdW1zZWFncmVlbjogMHgzY2IzNzEsXG4gIG1lZGl1bXNsYXRlYmx1ZTogMHg3YjY4ZWUsXG4gIG1lZGl1bXNwcmluZ2dyZWVuOiAweDAwZmE5YSxcbiAgbWVkaXVtdHVycXVvaXNlOiAweDQ4ZDFjYyxcbiAgbWVkaXVtdmlvbGV0cmVkOiAweGM3MTU4NSxcbiAgbWlkbmlnaHRibHVlOiAweDE5MTk3MCxcbiAgbWludGNyZWFtOiAweGY1ZmZmYSxcbiAgbWlzdHlyb3NlOiAweGZmZTRlMSxcbiAgbW9jY2FzaW46IDB4ZmZlNGI1LFxuICBuYXZham93aGl0ZTogMHhmZmRlYWQsXG4gIG5hdnk6IDB4MDAwMDgwLFxuICBvbGRsYWNlOiAweGZkZjVlNixcbiAgb2xpdmU6IDB4ODA4MDAwLFxuICBvbGl2ZWRyYWI6IDB4NmI4ZTIzLFxuICBvcmFuZ2U6IDB4ZmZhNTAwLFxuICBvcmFuZ2VyZWQ6IDB4ZmY0NTAwLFxuICBvcmNoaWQ6IDB4ZGE3MGQ2LFxuICBwYWxlZ29sZGVucm9kOiAweGVlZThhYSxcbiAgcGFsZWdyZWVuOiAweDk4ZmI5OCxcbiAgcGFsZXR1cnF1b2lzZTogMHhhZmVlZWUsXG4gIHBhbGV2aW9sZXRyZWQ6IDB4ZGI3MDkzLFxuICBwYXBheWF3aGlwOiAweGZmZWZkNSxcbiAgcGVhY2hwdWZmOiAweGZmZGFiOSxcbiAgcGVydTogMHhjZDg1M2YsXG4gIHBpbms6IDB4ZmZjMGNiLFxuICBwbHVtOiAweGRkYTBkZCxcbiAgcG93ZGVyYmx1ZTogMHhiMGUwZTYsXG4gIHB1cnBsZTogMHg4MDAwODAsXG4gIHJlYmVjY2FwdXJwbGU6IDB4NjYzMzk5LFxuICByZWQ6IDB4ZmYwMDAwLFxuICByb3N5YnJvd246IDB4YmM4ZjhmLFxuICByb3lhbGJsdWU6IDB4NDE2OWUxLFxuICBzYWRkbGVicm93bjogMHg4YjQ1MTMsXG4gIHNhbG1vbjogMHhmYTgwNzIsXG4gIHNhbmR5YnJvd246IDB4ZjRhNDYwLFxuICBzZWFncmVlbjogMHgyZThiNTcsXG4gIHNlYXNoZWxsOiAweGZmZjVlZSxcbiAgc2llbm5hOiAweGEwNTIyZCxcbiAgc2lsdmVyOiAweGMwYzBjMCxcbiAgc2t5Ymx1ZTogMHg4N2NlZWIsXG4gIHNsYXRlYmx1ZTogMHg2YTVhY2QsXG4gIHNsYXRlZ3JheTogMHg3MDgwOTAsXG4gIHNsYXRlZ3JleTogMHg3MDgwOTAsXG4gIHNub3c6IDB4ZmZmYWZhLFxuICBzcHJpbmdncmVlbjogMHgwMGZmN2YsXG4gIHN0ZWVsYmx1ZTogMHg0NjgyYjQsXG4gIHRhbjogMHhkMmI0OGMsXG4gIHRlYWw6IDB4MDA4MDgwLFxuICB0aGlzdGxlOiAweGQ4YmZkOCxcbiAgdG9tYXRvOiAweGZmNjM0NyxcbiAgdHVycXVvaXNlOiAweDQwZTBkMCxcbiAgdmlvbGV0OiAweGVlODJlZSxcbiAgd2hlYXQ6IDB4ZjVkZWIzLFxuICB3aGl0ZTogMHhmZmZmZmYsXG4gIHdoaXRlc21va2U6IDB4ZjVmNWY1LFxuICB5ZWxsb3c6IDB4ZmZmZjAwLFxuICB5ZWxsb3dncmVlbjogMHg5YWNkMzJcbn07XG5cbmRlZmluZShDb2xvciwgY29sb3IsIHtcbiAgY29weShjaGFubmVscykge1xuICAgIHJldHVybiBPYmplY3QuYXNzaWduKG5ldyB0aGlzLmNvbnN0cnVjdG9yLCB0aGlzLCBjaGFubmVscyk7XG4gIH0sXG4gIGRpc3BsYXlhYmxlKCkge1xuICAgIHJldHVybiB0aGlzLnJnYigpLmRpc3BsYXlhYmxlKCk7XG4gIH0sXG4gIGhleDogY29sb3JfZm9ybWF0SGV4LCAvLyBEZXByZWNhdGVkISBVc2UgY29sb3IuZm9ybWF0SGV4LlxuICBmb3JtYXRIZXg6IGNvbG9yX2Zvcm1hdEhleCxcbiAgZm9ybWF0SGV4ODogY29sb3JfZm9ybWF0SGV4OCxcbiAgZm9ybWF0SHNsOiBjb2xvcl9mb3JtYXRIc2wsXG4gIGZvcm1hdFJnYjogY29sb3JfZm9ybWF0UmdiLFxuICB0b1N0cmluZzogY29sb3JfZm9ybWF0UmdiXG59KTtcblxuZnVuY3Rpb24gY29sb3JfZm9ybWF0SGV4KCkge1xuICByZXR1cm4gdGhpcy5yZ2IoKS5mb3JtYXRIZXgoKTtcbn1cblxuZnVuY3Rpb24gY29sb3JfZm9ybWF0SGV4OCgpIHtcbiAgcmV0dXJuIHRoaXMucmdiKCkuZm9ybWF0SGV4OCgpO1xufVxuXG5mdW5jdGlvbiBjb2xvcl9mb3JtYXRIc2woKSB7XG4gIHJldHVybiBoc2xDb252ZXJ0KHRoaXMpLmZvcm1hdEhzbCgpO1xufVxuXG5mdW5jdGlvbiBjb2xvcl9mb3JtYXRSZ2IoKSB7XG4gIHJldHVybiB0aGlzLnJnYigpLmZvcm1hdFJnYigpO1xufVxuXG5leHBvcnQgZGVmYXVsdCBmdW5jdGlvbiBjb2xvcihmb3JtYXQpIHtcbiAgdmFyIG0sIGw7XG4gIGZvcm1hdCA9IChmb3JtYXQgKyBcIlwiKS50cmltKCkudG9Mb3dlckNhc2UoKTtcbiAgcmV0dXJuIChtID0gcmVIZXguZXhlYyhmb3JtYXQpKSA/IChsID0gbVsxXS5sZW5ndGgsIG0gPSBwYXJzZUludChtWzFdLCAxNiksIGwgPT09IDYgPyByZ2JuKG0pIC8vICNmZjAwMDBcbiAgICAgIDogbCA9PT0gMyA/IG5ldyBSZ2IoKG0gPj4gOCAmIDB4ZikgfCAobSA+PiA0ICYgMHhmMCksIChtID4+IDQgJiAweGYpIHwgKG0gJiAweGYwKSwgKChtICYgMHhmKSA8PCA0KSB8IChtICYgMHhmKSwgMSkgLy8gI2YwMFxuICAgICAgOiBsID09PSA4ID8gcmdiYShtID4+IDI0ICYgMHhmZiwgbSA+PiAxNiAmIDB4ZmYsIG0gPj4gOCAmIDB4ZmYsIChtICYgMHhmZikgLyAweGZmKSAvLyAjZmYwMDAwMDBcbiAgICAgIDogbCA9PT0gNCA/IHJnYmEoKG0gPj4gMTIgJiAweGYpIHwgKG0gPj4gOCAmIDB4ZjApLCAobSA+PiA4ICYgMHhmKSB8IChtID4+IDQgJiAweGYwKSwgKG0gPj4gNCAmIDB4ZikgfCAobSAmIDB4ZjApLCAoKChtICYgMHhmKSA8PCA0KSB8IChtICYgMHhmKSkgLyAweGZmKSAvLyAjZjAwMFxuICAgICAgOiBudWxsKSAvLyBpbnZhbGlkIGhleFxuICAgICAgOiAobSA9IHJlUmdiSW50ZWdlci5leGVjKGZvcm1hdCkpID8gbmV3IFJnYihtWzFdLCBtWzJdLCBtWzNdLCAxKSAvLyByZ2IoMjU1LCAwLCAwKVxuICAgICAgOiAobSA9IHJlUmdiUGVyY2VudC5leGVjKGZvcm1hdCkpID8gbmV3IFJnYihtWzFdICogMjU1IC8gMTAwLCBtWzJdICogMjU1IC8gMTAwLCBtWzNdICogMjU1IC8gMTAwLCAxKSAvLyByZ2IoMTAwJSwgMCUsIDAlKVxuICAgICAgOiAobSA9IHJlUmdiYUludGVnZXIuZXhlYyhmb3JtYXQpKSA/IHJnYmEobVsxXSwgbVsyXSwgbVszXSwgbVs0XSkgLy8gcmdiYSgyNTUsIDAsIDAsIDEpXG4gICAgICA6IChtID0gcmVSZ2JhUGVyY2VudC5leGVjKGZvcm1hdCkpID8gcmdiYShtWzFdICogMjU1IC8gMTAwLCBtWzJdICogMjU1IC8gMTAwLCBtWzNdICogMjU1IC8gMTAwLCBtWzRdKSAvLyByZ2IoMTAwJSwgMCUsIDAlLCAxKVxuICAgICAgOiAobSA9IHJlSHNsUGVyY2VudC5leGVjKGZvcm1hdCkpID8gaHNsYShtWzFdLCBtWzJdIC8gMTAwLCBtWzNdIC8gMTAwLCAxKSAvLyBoc2woMTIwLCA1MCUsIDUwJSlcbiAgICAgIDogKG0gPSByZUhzbGFQZXJjZW50LmV4ZWMoZm9ybWF0KSkgPyBoc2xhKG1bMV0sIG1bMl0gLyAxMDAsIG1bM10gLyAxMDAsIG1bNF0pIC8vIGhzbGEoMTIwLCA1MCUsIDUwJSwgMSlcbiAgICAgIDogbmFtZWQuaGFzT3duUHJvcGVydHkoZm9ybWF0KSA/IHJnYm4obmFtZWRbZm9ybWF0XSkgLy8gZXNsaW50LWRpc2FibGUtbGluZSBuby1wcm90b3R5cGUtYnVpbHRpbnNcbiAgICAgIDogZm9ybWF0ID09PSBcInRyYW5zcGFyZW50XCIgPyBuZXcgUmdiKE5hTiwgTmFOLCBOYU4sIDApXG4gICAgICA6IG51bGw7XG59XG5cbmZ1bmN0aW9uIHJnYm4obikge1xuICByZXR1cm4gbmV3IFJnYihuID4+IDE2ICYgMHhmZiwgbiA+PiA4ICYgMHhmZiwgbiAmIDB4ZmYsIDEpO1xufVxuXG5mdW5jdGlvbiByZ2JhKHIsIGcsIGIsIGEpIHtcbiAgaWYgKGEgPD0gMCkgciA9IGcgPSBiID0gTmFOO1xuICByZXR1cm4gbmV3IFJnYihyLCBnLCBiLCBhKTtcbn1cblxuZXhwb3J0IGZ1bmN0aW9uIHJnYkNvbnZlcnQobykge1xuICBpZiAoIShvIGluc3RhbmNlb2YgQ29sb3IpKSBvID0gY29sb3Iobyk7XG4gIGlmICghbykgcmV0dXJuIG5ldyBSZ2I7XG4gIG8gPSBvLnJnYigpO1xuICByZXR1cm4gbmV3IFJnYihvLnIsIG8uZywgby5iLCBvLm9wYWNpdHkpO1xufVxuXG5leHBvcnQgZnVuY3Rpb24gcmdiKHIsIGcsIGIsIG9wYWNpdHkpIHtcbiAgcmV0dXJuIGFyZ3VtZW50cy5sZW5ndGggPT09IDEgPyByZ2JDb252ZXJ0KHIpIDogbmV3IFJnYihyLCBnLCBiLCBvcGFjaXR5ID09IG51bGwgPyAxIDogb3BhY2l0eSk7XG59XG5cbmV4cG9ydCBmdW5jdGlvbiBSZ2IociwgZywgYiwgb3BhY2l0eSkge1xuICB0aGlzLnIgPSArcjtcbiAgdGhpcy5nID0gK2c7XG4gIHRoaXMuYiA9ICtiO1xuICB0aGlzLm9wYWNpdHkgPSArb3BhY2l0eTtcbn1cblxuZGVmaW5lKFJnYiwgcmdiLCBleHRlbmQoQ29sb3IsIHtcbiAgYnJpZ2h0ZXIoaykge1xuICAgIGsgPSBrID09IG51bGwgPyBicmlnaHRlciA6IE1hdGgucG93KGJyaWdodGVyLCBrKTtcbiAgICByZXR1cm4gbmV3IFJnYih0aGlzLnIgKiBrLCB0aGlzLmcgKiBrLCB0aGlzLmIgKiBrLCB0aGlzLm9wYWNpdHkpO1xuICB9LFxuICBkYXJrZXIoaykge1xuICAgIGsgPSBrID09IG51bGwgPyBkYXJrZXIgOiBNYXRoLnBvdyhkYXJrZXIsIGspO1xuICAgIHJldHVybiBuZXcgUmdiKHRoaXMuciAqIGssIHRoaXMuZyAqIGssIHRoaXMuYiAqIGssIHRoaXMub3BhY2l0eSk7XG4gIH0sXG4gIHJnYigpIHtcbiAgICByZXR1cm4gdGhpcztcbiAgfSxcbiAgY2xhbXAoKSB7XG4gICAgcmV0dXJuIG5ldyBSZ2IoY2xhbXBpKHRoaXMuciksIGNsYW1waSh0aGlzLmcpLCBjbGFtcGkodGhpcy5iKSwgY2xhbXBhKHRoaXMub3BhY2l0eSkpO1xuICB9LFxuICBkaXNwbGF5YWJsZSgpIHtcbiAgICByZXR1cm4gKC0wLjUgPD0gdGhpcy5yICYmIHRoaXMuciA8IDI1NS41KVxuICAgICAgICAmJiAoLTAuNSA8PSB0aGlzLmcgJiYgdGhpcy5nIDwgMjU1LjUpXG4gICAgICAgICYmICgtMC41IDw9IHRoaXMuYiAmJiB0aGlzLmIgPCAyNTUuNSlcbiAgICAgICAgJiYgKDAgPD0gdGhpcy5vcGFjaXR5ICYmIHRoaXMub3BhY2l0eSA8PSAxKTtcbiAgfSxcbiAgaGV4OiByZ2JfZm9ybWF0SGV4LCAvLyBEZXByZWNhdGVkISBVc2UgY29sb3IuZm9ybWF0SGV4LlxuICBmb3JtYXRIZXg6IHJnYl9mb3JtYXRIZXgsXG4gIGZvcm1hdEhleDg6IHJnYl9mb3JtYXRIZXg4LFxuICBmb3JtYXRSZ2I6IHJnYl9mb3JtYXRSZ2IsXG4gIHRvU3RyaW5nOiByZ2JfZm9ybWF0UmdiXG59KSk7XG5cbmZ1bmN0aW9uIHJnYl9mb3JtYXRIZXgoKSB7XG4gIHJldHVybiBgIyR7aGV4KHRoaXMucil9JHtoZXgodGhpcy5nKX0ke2hleCh0aGlzLmIpfWA7XG59XG5cbmZ1bmN0aW9uIHJnYl9mb3JtYXRIZXg4KCkge1xuICByZXR1cm4gYCMke2hleCh0aGlzLnIpfSR7aGV4KHRoaXMuZyl9JHtoZXgodGhpcy5iKX0ke2hleCgoaXNOYU4odGhpcy5vcGFjaXR5KSA/IDEgOiB0aGlzLm9wYWNpdHkpICogMjU1KX1gO1xufVxuXG5mdW5jdGlvbiByZ2JfZm9ybWF0UmdiKCkge1xuICBjb25zdCBhID0gY2xhbXBhKHRoaXMub3BhY2l0eSk7XG4gIHJldHVybiBgJHthID09PSAxID8gXCJyZ2IoXCIgOiBcInJnYmEoXCJ9JHtjbGFtcGkodGhpcy5yKX0sICR7Y2xhbXBpKHRoaXMuZyl9LCAke2NsYW1waSh0aGlzLmIpfSR7YSA9PT0gMSA/IFwiKVwiIDogYCwgJHthfSlgfWA7XG59XG5cbmZ1bmN0aW9uIGNsYW1wYShvcGFjaXR5KSB7XG4gIHJldHVybiBpc05hTihvcGFjaXR5KSA/IDEgOiBNYXRoLm1heCgwLCBNYXRoLm1pbigxLCBvcGFjaXR5KSk7XG59XG5cbmZ1bmN0aW9uIGNsYW1waSh2YWx1ZSkge1xuICByZXR1cm4gTWF0aC5tYXgoMCwgTWF0aC5taW4oMjU1LCBNYXRoLnJvdW5kKHZhbHVlKSB8fCAwKSk7XG59XG5cbmZ1bmN0aW9uIGhleCh2YWx1ZSkge1xuICB2YWx1ZSA9IGNsYW1waSh2YWx1ZSk7XG4gIHJldHVybiAodmFsdWUgPCAxNiA/IFwiMFwiIDogXCJcIikgKyB2YWx1ZS50b1N0cmluZygxNik7XG59XG5cbmZ1bmN0aW9uIGhzbGEoaCwgcywgbCwgYSkge1xuICBpZiAoYSA8PSAwKSBoID0gcyA9IGwgPSBOYU47XG4gIGVsc2UgaWYgKGwgPD0gMCB8fCBsID49IDEpIGggPSBzID0gTmFOO1xuICBlbHNlIGlmIChzIDw9IDApIGggPSBOYU47XG4gIHJldHVybiBuZXcgSHNsKGgsIHMsIGwsIGEpO1xufVxuXG5leHBvcnQgZnVuY3Rpb24gaHNsQ29udmVydChvKSB7XG4gIGlmIChvIGluc3RhbmNlb2YgSHNsKSByZXR1cm4gbmV3IEhzbChvLmgsIG8ucywgby5sLCBvLm9wYWNpdHkpO1xuICBpZiAoIShvIGluc3RhbmNlb2YgQ29sb3IpKSBvID0gY29sb3Iobyk7XG4gIGlmICghbykgcmV0dXJuIG5ldyBIc2w7XG4gIGlmIChvIGluc3RhbmNlb2YgSHNsKSByZXR1cm4gbztcbiAgbyA9IG8ucmdiKCk7XG4gIHZhciByID0gby5yIC8gMjU1LFxuICAgICAgZyA9IG8uZyAvIDI1NSxcbiAgICAgIGIgPSBvLmIgLyAyNTUsXG4gICAgICBtaW4gPSBNYXRoLm1pbihyLCBnLCBiKSxcbiAgICAgIG1heCA9IE1hdGgubWF4KHIsIGcsIGIpLFxuICAgICAgaCA9IE5hTixcbiAgICAgIHMgPSBtYXggLSBtaW4sXG4gICAgICBsID0gKG1heCArIG1pbikgLyAyO1xuICBpZiAocykge1xuICAgIGlmIChyID09PSBtYXgpIGggPSAoZyAtIGIpIC8gcyArIChnIDwgYikgKiA2O1xuICAgIGVsc2UgaWYgKGcgPT09IG1heCkgaCA9IChiIC0gcikgLyBzICsgMjtcbiAgICBlbHNlIGggPSAociAtIGcpIC8gcyArIDQ7XG4gICAgcyAvPSBsIDwgMC41ID8gbWF4ICsgbWluIDogMiAtIG1heCAtIG1pbjtcbiAgICBoICo9IDYwO1xuICB9IGVsc2Uge1xuICAgIHMgPSBsID4gMCAmJiBsIDwgMSA/IDAgOiBoO1xuICB9XG4gIHJldHVybiBuZXcgSHNsKGgsIHMsIGwsIG8ub3BhY2l0eSk7XG59XG5cbmV4cG9ydCBmdW5jdGlvbiBoc2woaCwgcywgbCwgb3BhY2l0eSkge1xuICByZXR1cm4gYXJndW1lbnRzLmxlbmd0aCA9PT0gMSA/IGhzbENvbnZlcnQoaCkgOiBuZXcgSHNsKGgsIHMsIGwsIG9wYWNpdHkgPT0gbnVsbCA/IDEgOiBvcGFjaXR5KTtcbn1cblxuZnVuY3Rpb24gSHNsKGgsIHMsIGwsIG9wYWNpdHkpIHtcbiAgdGhpcy5oID0gK2g7XG4gIHRoaXMucyA9ICtzO1xuICB0aGlzLmwgPSArbDtcbiAgdGhpcy5vcGFjaXR5ID0gK29wYWNpdHk7XG59XG5cbmRlZmluZShIc2wsIGhzbCwgZXh0ZW5kKENvbG9yLCB7XG4gIGJyaWdodGVyKGspIHtcbiAgICBrID0gayA9PSBudWxsID8gYnJpZ2h0ZXIgOiBNYXRoLnBvdyhicmlnaHRlciwgayk7XG4gICAgcmV0dXJuIG5ldyBIc2wodGhpcy5oLCB0aGlzLnMsIHRoaXMubCAqIGssIHRoaXMub3BhY2l0eSk7XG4gIH0sXG4gIGRhcmtlcihrKSB7XG4gICAgayA9IGsgPT0gbnVsbCA/IGRhcmtlciA6IE1hdGgucG93KGRhcmtlciwgayk7XG4gICAgcmV0dXJuIG5ldyBIc2wodGhpcy5oLCB0aGlzLnMsIHRoaXMubCAqIGssIHRoaXMub3BhY2l0eSk7XG4gIH0sXG4gIHJnYigpIHtcbiAgICB2YXIgaCA9IHRoaXMuaCAlIDM2MCArICh0aGlzLmggPCAwKSAqIDM2MCxcbiAgICAgICAgcyA9IGlzTmFOKGgpIHx8IGlzTmFOKHRoaXMucykgPyAwIDogdGhpcy5zLFxuICAgICAgICBsID0gdGhpcy5sLFxuICAgICAgICBtMiA9IGwgKyAobCA8IDAuNSA/IGwgOiAxIC0gbCkgKiBzLFxuICAgICAgICBtMSA9IDIgKiBsIC0gbTI7XG4gICAgcmV0dXJuIG5ldyBSZ2IoXG4gICAgICBoc2wycmdiKGggPj0gMjQwID8gaCAtIDI0MCA6IGggKyAxMjAsIG0xLCBtMiksXG4gICAgICBoc2wycmdiKGgsIG0xLCBtMiksXG4gICAgICBoc2wycmdiKGggPCAxMjAgPyBoICsgMjQwIDogaCAtIDEyMCwgbTEsIG0yKSxcbiAgICAgIHRoaXMub3BhY2l0eVxuICAgICk7XG4gIH0sXG4gIGNsYW1wKCkge1xuICAgIHJldHVybiBuZXcgSHNsKGNsYW1waCh0aGlzLmgpLCBjbGFtcHQodGhpcy5zKSwgY2xhbXB0KHRoaXMubCksIGNsYW1wYSh0aGlzLm9wYWNpdHkpKTtcbiAgfSxcbiAgZGlzcGxheWFibGUoKSB7XG4gICAgcmV0dXJuICgwIDw9IHRoaXMucyAmJiB0aGlzLnMgPD0gMSB8fCBpc05hTih0aGlzLnMpKVxuICAgICAgICAmJiAoMCA8PSB0aGlzLmwgJiYgdGhpcy5sIDw9IDEpXG4gICAgICAgICYmICgwIDw9IHRoaXMub3BhY2l0eSAmJiB0aGlzLm9wYWNpdHkgPD0gMSk7XG4gIH0sXG4gIGZvcm1hdEhzbCgpIHtcbiAgICBjb25zdCBhID0gY2xhbXBhKHRoaXMub3BhY2l0eSk7XG4gICAgcmV0dXJuIGAke2EgPT09IDEgPyBcImhzbChcIiA6IFwiaHNsYShcIn0ke2NsYW1waCh0aGlzLmgpfSwgJHtjbGFtcHQodGhpcy5zKSAqIDEwMH0lLCAke2NsYW1wdCh0aGlzLmwpICogMTAwfSUke2EgPT09IDEgPyBcIilcIiA6IGAsICR7YX0pYH1gO1xuICB9XG59KSk7XG5cbmZ1bmN0aW9uIGNsYW1waCh2YWx1ZSkge1xuICB2YWx1ZSA9ICh2YWx1ZSB8fCAwKSAlIDM2MDtcbiAgcmV0dXJuIHZhbHVlIDwgMCA/IHZhbHVlICsgMzYwIDogdmFsdWU7XG59XG5cbmZ1bmN0aW9uIGNsYW1wdCh2YWx1ZSkge1xuICByZXR1cm4gTWF0aC5tYXgoMCwgTWF0aC5taW4oMSwgdmFsdWUgfHwgMCkpO1xufVxuXG4vKiBGcm9tIEZ2RCAxMy4zNywgQ1NTIENvbG9yIE1vZHVsZSBMZXZlbCAzICovXG5mdW5jdGlvbiBoc2wycmdiKGgsIG0xLCBtMikge1xuICByZXR1cm4gKGggPCA2MCA/IG0xICsgKG0yIC0gbTEpICogaCAvIDYwXG4gICAgICA6IGggPCAxODAgPyBtMlxuICAgICAgOiBoIDwgMjQwID8gbTEgKyAobTIgLSBtMSkgKiAoMjQwIC0gaCkgLyA2MFxuICAgICAgOiBtMSkgKiAyNTU7XG59XG4iLCJleHBvcnQgZGVmYXVsdCB4ID0+ICgpID0+IHg7XG4iLCJpbXBvcnQgY29uc3RhbnQgZnJvbSBcIi4vY29uc3RhbnQuanNcIjtcblxuZnVuY3Rpb24gbGluZWFyKGEsIGQpIHtcbiAgcmV0dXJuIGZ1bmN0aW9uKHQpIHtcbiAgICByZXR1cm4gYSArIHQgKiBkO1xuICB9O1xufVxuXG5mdW5jdGlvbiBleHBvbmVudGlhbChhLCBiLCB5KSB7XG4gIHJldHVybiBhID0gTWF0aC5wb3coYSwgeSksIGIgPSBNYXRoLnBvdyhiLCB5KSAtIGEsIHkgPSAxIC8geSwgZnVuY3Rpb24odCkge1xuICAgIHJldHVybiBNYXRoLnBvdyhhICsgdCAqIGIsIHkpO1xuICB9O1xufVxuXG5leHBvcnQgZnVuY3Rpb24gaHVlKGEsIGIpIHtcbiAgdmFyIGQgPSBiIC0gYTtcbiAgcmV0dXJuIGQgPyBsaW5lYXIoYSwgZCA+IDE4MCB8fCBkIDwgLTE4MCA/IGQgLSAzNjAgKiBNYXRoLnJvdW5kKGQgLyAzNjApIDogZCkgOiBjb25zdGFudChpc05hTihhKSA/IGIgOiBhKTtcbn1cblxuZXhwb3J0IGZ1bmN0aW9uIGdhbW1hKHkpIHtcbiAgcmV0dXJuICh5ID0gK3kpID09PSAxID8gbm9nYW1tYSA6IGZ1bmN0aW9uKGEsIGIpIHtcbiAgICByZXR1cm4gYiAtIGEgPyBleHBvbmVudGlhbChhLCBiLCB5KSA6IGNvbnN0YW50KGlzTmFOKGEpID8gYiA6IGEpO1xuICB9O1xufVxuXG5leHBvcnQgZGVmYXVsdCBmdW5jdGlvbiBub2dhbW1hKGEsIGIpIHtcbiAgdmFyIGQgPSBiIC0gYTtcbiAgcmV0dXJuIGQgPyBsaW5lYXIoYSwgZCkgOiBjb25zdGFudChpc05hTihhKSA/IGIgOiBhKTtcbn1cbiIsImltcG9ydCB7cmdiIGFzIGNvbG9yUmdifSBmcm9tIFwiZDMtY29sb3JcIjtcbmltcG9ydCBiYXNpcyBmcm9tIFwiLi9iYXNpcy5qc1wiO1xuaW1wb3J0IGJhc2lzQ2xvc2VkIGZyb20gXCIuL2Jhc2lzQ2xvc2VkLmpzXCI7XG5pbXBvcnQgbm9nYW1tYSwge2dhbW1hfSBmcm9tIFwiLi9jb2xvci5qc1wiO1xuXG5leHBvcnQgZGVmYXVsdCAoZnVuY3Rpb24gcmdiR2FtbWEoeSkge1xuICB2YXIgY29sb3IgPSBnYW1tYSh5KTtcblxuICBmdW5jdGlvbiByZ2Ioc3RhcnQsIGVuZCkge1xuICAgIHZhciByID0gY29sb3IoKHN0YXJ0ID0gY29sb3JSZ2Ioc3RhcnQpKS5yLCAoZW5kID0gY29sb3JSZ2IoZW5kKSkuciksXG4gICAgICAgIGcgPSBjb2xvcihzdGFydC5nLCBlbmQuZyksXG4gICAgICAgIGIgPSBjb2xvcihzdGFydC5iLCBlbmQuYiksXG4gICAgICAgIG9wYWNpdHkgPSBub2dhbW1hKHN0YXJ0Lm9wYWNpdHksIGVuZC5vcGFjaXR5KTtcbiAgICByZXR1cm4gZnVuY3Rpb24odCkge1xuICAgICAgc3RhcnQuciA9IHIodCk7XG4gICAgICBzdGFydC5nID0gZyh0KTtcbiAgICAgIHN0YXJ0LmIgPSBiKHQpO1xuICAgICAgc3RhcnQub3BhY2l0eSA9IG9wYWNpdHkodCk7XG4gICAgICByZXR1cm4gc3RhcnQgKyBcIlwiO1xuICAgIH07XG4gIH1cblxuICByZ2IuZ2FtbWEgPSByZ2JHYW1tYTtcblxuICByZXR1cm4gcmdiO1xufSkoMSk7XG5cbmZ1bmN0aW9uIHJnYlNwbGluZShzcGxpbmUpIHtcbiAgcmV0dXJuIGZ1bmN0aW9uKGNvbG9ycykge1xuICAgIHZhciBuID0gY29sb3JzLmxlbmd0aCxcbiAgICAgICAgciA9IG5ldyBBcnJheShuKSxcbiAgICAgICAgZyA9IG5ldyBBcnJheShuKSxcbiAgICAgICAgYiA9IG5ldyBBcnJheShuKSxcbiAgICAgICAgaSwgY29sb3I7XG4gICAgZm9yIChpID0gMDsgaSA8IG47ICsraSkge1xuICAgICAgY29sb3IgPSBjb2xvclJnYihjb2xvcnNbaV0pO1xuICAgICAgcltpXSA9IGNvbG9yLnIgfHwgMDtcbiAgICAgIGdbaV0gPSBjb2xvci5nIHx8IDA7XG4gICAgICBiW2ldID0gY29sb3IuYiB8fCAwO1xuICAgIH1cbiAgICByID0gc3BsaW5lKHIpO1xuICAgIGcgPSBzcGxpbmUoZyk7XG4gICAgYiA9IHNwbGluZShiKTtcbiAgICBjb2xvci5vcGFjaXR5ID0gMTtcbiAgICByZXR1cm4gZnVuY3Rpb24odCkge1xuICAgICAgY29sb3IuciA9IHIodCk7XG4gICAgICBjb2xvci5nID0gZyh0KTtcbiAgICAgIGNvbG9yLmIgPSBiKHQpO1xuICAgICAgcmV0dXJuIGNvbG9yICsgXCJcIjtcbiAgICB9O1xuICB9O1xufVxuXG5leHBvcnQgdmFyIHJnYkJhc2lzID0gcmdiU3BsaW5lKGJhc2lzKTtcbmV4cG9ydCB2YXIgcmdiQmFzaXNDbG9zZWQgPSByZ2JTcGxpbmUoYmFzaXNDbG9zZWQpO1xuIiwiZXhwb3J0IGRlZmF1bHQgZnVuY3Rpb24oYSwgYikge1xuICByZXR1cm4gYSA9ICthLCBiID0gK2IsIGZ1bmN0aW9uKHQpIHtcbiAgICByZXR1cm4gYSAqICgxIC0gdCkgKyBiICogdDtcbiAgfTtcbn1cbiIsImltcG9ydCBudW1iZXIgZnJvbSBcIi4vbnVtYmVyLmpzXCI7XG5cbnZhciByZUEgPSAvWy0rXT8oPzpcXGQrXFwuP1xcZCp8XFwuP1xcZCspKD86W2VFXVstK10/XFxkKyk/L2csXG4gICAgcmVCID0gbmV3IFJlZ0V4cChyZUEuc291cmNlLCBcImdcIik7XG5cbmZ1bmN0aW9uIHplcm8oYikge1xuICByZXR1cm4gZnVuY3Rpb24oKSB7XG4gICAgcmV0dXJuIGI7XG4gIH07XG59XG5cbmZ1bmN0aW9uIG9uZShiKSB7XG4gIHJldHVybiBmdW5jdGlvbih0KSB7XG4gICAgcmV0dXJuIGIodCkgKyBcIlwiO1xuICB9O1xufVxuXG5leHBvcnQgZGVmYXVsdCBmdW5jdGlvbihhLCBiKSB7XG4gIHZhciBiaSA9IHJlQS5sYXN0SW5kZXggPSByZUIubGFzdEluZGV4ID0gMCwgLy8gc2NhbiBpbmRleCBmb3IgbmV4dCBudW1iZXIgaW4gYlxuICAgICAgYW0sIC8vIGN1cnJlbnQgbWF0Y2ggaW4gYVxuICAgICAgYm0sIC8vIGN1cnJlbnQgbWF0Y2ggaW4gYlxuICAgICAgYnMsIC8vIHN0cmluZyBwcmVjZWRpbmcgY3VycmVudCBudW1iZXIgaW4gYiwgaWYgYW55XG4gICAgICBpID0gLTEsIC8vIGluZGV4IGluIHNcbiAgICAgIHMgPSBbXSwgLy8gc3RyaW5nIGNvbnN0YW50cyBhbmQgcGxhY2Vob2xkZXJzXG4gICAgICBxID0gW107IC8vIG51bWJlciBpbnRlcnBvbGF0b3JzXG5cbiAgLy8gQ29lcmNlIGlucHV0cyB0byBzdHJpbmdzLlxuICBhID0gYSArIFwiXCIsIGIgPSBiICsgXCJcIjtcblxuICAvLyBJbnRlcnBvbGF0ZSBwYWlycyBvZiBudW1iZXJzIGluIGEgJiBiLlxuICB3aGlsZSAoKGFtID0gcmVBLmV4ZWMoYSkpXG4gICAgICAmJiAoYm0gPSByZUIuZXhlYyhiKSkpIHtcbiAgICBpZiAoKGJzID0gYm0uaW5kZXgpID4gYmkpIHsgLy8gYSBzdHJpbmcgcHJlY2VkZXMgdGhlIG5leHQgbnVtYmVyIGluIGJcbiAgICAgIGJzID0gYi5zbGljZShiaSwgYnMpO1xuICAgICAgaWYgKHNbaV0pIHNbaV0gKz0gYnM7IC8vIGNvYWxlc2NlIHdpdGggcHJldmlvdXMgc3RyaW5nXG4gICAgICBlbHNlIHNbKytpXSA9IGJzO1xuICAgIH1cbiAgICBpZiAoKGFtID0gYW1bMF0pID09PSAoYm0gPSBibVswXSkpIHsgLy8gbnVtYmVycyBpbiBhICYgYiBtYXRjaFxuICAgICAgaWYgKHNbaV0pIHNbaV0gKz0gYm07IC8vIGNvYWxlc2NlIHdpdGggcHJldmlvdXMgc3RyaW5nXG4gICAgICBlbHNlIHNbKytpXSA9IGJtO1xuICAgIH0gZWxzZSB7IC8vIGludGVycG9sYXRlIG5vbi1tYXRjaGluZyBudW1iZXJzXG4gICAgICBzWysraV0gPSBudWxsO1xuICAgICAgcS5wdXNoKHtpOiBpLCB4OiBudW1iZXIoYW0sIGJtKX0pO1xuICAgIH1cbiAgICBiaSA9IHJlQi5sYXN0SW5kZXg7XG4gIH1cblxuICAvLyBBZGQgcmVtYWlucyBvZiBiLlxuICBpZiAoYmkgPCBiLmxlbmd0aCkge1xuICAgIGJzID0gYi5zbGljZShiaSk7XG4gICAgaWYgKHNbaV0pIHNbaV0gKz0gYnM7IC8vIGNvYWxlc2NlIHdpdGggcHJldmlvdXMgc3RyaW5nXG4gICAgZWxzZSBzWysraV0gPSBicztcbiAgfVxuXG4gIC8vIFNwZWNpYWwgb3B0aW1pemF0aW9uIGZvciBvbmx5IGEgc2luZ2xlIG1hdGNoLlxuICAvLyBPdGhlcndpc2UsIGludGVycG9sYXRlIGVhY2ggb2YgdGhlIG51bWJlcnMgYW5kIHJlam9pbiB0aGUgc3RyaW5nLlxuICByZXR1cm4gcy5sZW5ndGggPCAyID8gKHFbMF1cbiAgICAgID8gb25lKHFbMF0ueClcbiAgICAgIDogemVybyhiKSlcbiAgICAgIDogKGIgPSBxLmxlbmd0aCwgZnVuY3Rpb24odCkge1xuICAgICAgICAgIGZvciAodmFyIGkgPSAwLCBvOyBpIDwgYjsgKytpKSBzWyhvID0gcVtpXSkuaV0gPSBvLngodCk7XG4gICAgICAgICAgcmV0dXJuIHMuam9pbihcIlwiKTtcbiAgICAgICAgfSk7XG59XG4iLCJ2YXIgZGVncmVlcyA9IDE4MCAvIE1hdGguUEk7XG5cbmV4cG9ydCB2YXIgaWRlbnRpdHkgPSB7XG4gIHRyYW5zbGF0ZVg6IDAsXG4gIHRyYW5zbGF0ZVk6IDAsXG4gIHJvdGF0ZTogMCxcbiAgc2tld1g6IDAsXG4gIHNjYWxlWDogMSxcbiAgc2NhbGVZOiAxXG59O1xuXG5leHBvcnQgZGVmYXVsdCBmdW5jdGlvbihhLCBiLCBjLCBkLCBlLCBmKSB7XG4gIHZhciBzY2FsZVgsIHNjYWxlWSwgc2tld1g7XG4gIGlmIChzY2FsZVggPSBNYXRoLnNxcnQoYSAqIGEgKyBiICogYikpIGEgLz0gc2NhbGVYLCBiIC89IHNjYWxlWDtcbiAgaWYgKHNrZXdYID0gYSAqIGMgKyBiICogZCkgYyAtPSBhICogc2tld1gsIGQgLT0gYiAqIHNrZXdYO1xuICBpZiAoc2NhbGVZID0gTWF0aC5zcXJ0KGMgKiBjICsgZCAqIGQpKSBjIC89IHNjYWxlWSwgZCAvPSBzY2FsZVksIHNrZXdYIC89IHNjYWxlWTtcbiAgaWYgKGEgKiBkIDwgYiAqIGMpIGEgPSAtYSwgYiA9IC1iLCBza2V3WCA9IC1za2V3WCwgc2NhbGVYID0gLXNjYWxlWDtcbiAgcmV0dXJuIHtcbiAgICB0cmFuc2xhdGVYOiBlLFxuICAgIHRyYW5zbGF0ZVk6IGYsXG4gICAgcm90YXRlOiBNYXRoLmF0YW4yKGIsIGEpICogZGVncmVlcyxcbiAgICBza2V3WDogTWF0aC5hdGFuKHNrZXdYKSAqIGRlZ3JlZXMsXG4gICAgc2NhbGVYOiBzY2FsZVgsXG4gICAgc2NhbGVZOiBzY2FsZVlcbiAgfTtcbn1cbiIsImltcG9ydCBkZWNvbXBvc2UsIHtpZGVudGl0eX0gZnJvbSBcIi4vZGVjb21wb3NlLmpzXCI7XG5cbnZhciBzdmdOb2RlO1xuXG4vKiBlc2xpbnQtZGlzYWJsZSBuby11bmRlZiAqL1xuZXhwb3J0IGZ1bmN0aW9uIHBhcnNlQ3NzKHZhbHVlKSB7XG4gIGNvbnN0IG0gPSBuZXcgKHR5cGVvZiBET01NYXRyaXggPT09IFwiZnVuY3Rpb25cIiA/IERPTU1hdHJpeCA6IFdlYktpdENTU01hdHJpeCkodmFsdWUgKyBcIlwiKTtcbiAgcmV0dXJuIG0uaXNJZGVudGl0eSA/IGlkZW50aXR5IDogZGVjb21wb3NlKG0uYSwgbS5iLCBtLmMsIG0uZCwgbS5lLCBtLmYpO1xufVxuXG5leHBvcnQgZnVuY3Rpb24gcGFyc2VTdmcodmFsdWUpIHtcbiAgaWYgKHZhbHVlID09IG51bGwpIHJldHVybiBpZGVudGl0eTtcbiAgaWYgKCFzdmdOb2RlKSBzdmdOb2RlID0gZG9jdW1lbnQuY3JlYXRlRWxlbWVudE5TKFwiaHR0cDovL3d3dy53My5vcmcvMjAwMC9zdmdcIiwgXCJnXCIpO1xuICBzdmdOb2RlLnNldEF0dHJpYnV0ZShcInRyYW5zZm9ybVwiLCB2YWx1ZSk7XG4gIGlmICghKHZhbHVlID0gc3ZnTm9kZS50cmFuc2Zvcm0uYmFzZVZhbC5jb25zb2xpZGF0ZSgpKSkgcmV0dXJuIGlkZW50aXR5O1xuICB2YWx1ZSA9IHZhbHVlLm1hdHJpeDtcbiAgcmV0dXJuIGRlY29tcG9zZSh2YWx1ZS5hLCB2YWx1ZS5iLCB2YWx1ZS5jLCB2YWx1ZS5kLCB2YWx1ZS5lLCB2YWx1ZS5mKTtcbn1cbiIsImltcG9ydCBudW1iZXIgZnJvbSBcIi4uL251bWJlci5qc1wiO1xuaW1wb3J0IHtwYXJzZUNzcywgcGFyc2VTdmd9IGZyb20gXCIuL3BhcnNlLmpzXCI7XG5cbmZ1bmN0aW9uIGludGVycG9sYXRlVHJhbnNmb3JtKHBhcnNlLCBweENvbW1hLCBweFBhcmVuLCBkZWdQYXJlbikge1xuXG4gIGZ1bmN0aW9uIHBvcChzKSB7XG4gICAgcmV0dXJuIHMubGVuZ3RoID8gcy5wb3AoKSArIFwiIFwiIDogXCJcIjtcbiAgfVxuXG4gIGZ1bmN0aW9uIHRyYW5zbGF0ZSh4YSwgeWEsIHhiLCB5YiwgcywgcSkge1xuICAgIGlmICh4YSAhPT0geGIgfHwgeWEgIT09IHliKSB7XG4gICAgICB2YXIgaSA9IHMucHVzaChcInRyYW5zbGF0ZShcIiwgbnVsbCwgcHhDb21tYSwgbnVsbCwgcHhQYXJlbik7XG4gICAgICBxLnB1c2goe2k6IGkgLSA0LCB4OiBudW1iZXIoeGEsIHhiKX0sIHtpOiBpIC0gMiwgeDogbnVtYmVyKHlhLCB5Yil9KTtcbiAgICB9IGVsc2UgaWYgKHhiIHx8IHliKSB7XG4gICAgICBzLnB1c2goXCJ0cmFuc2xhdGUoXCIgKyB4YiArIHB4Q29tbWEgKyB5YiArIHB4UGFyZW4pO1xuICAgIH1cbiAgfVxuXG4gIGZ1bmN0aW9uIHJvdGF0ZShhLCBiLCBzLCBxKSB7XG4gICAgaWYgKGEgIT09IGIpIHtcbiAgICAgIGlmIChhIC0gYiA+IDE4MCkgYiArPSAzNjA7IGVsc2UgaWYgKGIgLSBhID4gMTgwKSBhICs9IDM2MDsgLy8gc2hvcnRlc3QgcGF0aFxuICAgICAgcS5wdXNoKHtpOiBzLnB1c2gocG9wKHMpICsgXCJyb3RhdGUoXCIsIG51bGwsIGRlZ1BhcmVuKSAtIDIsIHg6IG51bWJlcihhLCBiKX0pO1xuICAgIH0gZWxzZSBpZiAoYikge1xuICAgICAgcy5wdXNoKHBvcChzKSArIFwicm90YXRlKFwiICsgYiArIGRlZ1BhcmVuKTtcbiAgICB9XG4gIH1cblxuICBmdW5jdGlvbiBza2V3WChhLCBiLCBzLCBxKSB7XG4gICAgaWYgKGEgIT09IGIpIHtcbiAgICAgIHEucHVzaCh7aTogcy5wdXNoKHBvcChzKSArIFwic2tld1goXCIsIG51bGwsIGRlZ1BhcmVuKSAtIDIsIHg6IG51bWJlcihhLCBiKX0pO1xuICAgIH0gZWxzZSBpZiAoYikge1xuICAgICAgcy5wdXNoKHBvcChzKSArIFwic2tld1goXCIgKyBiICsgZGVnUGFyZW4pO1xuICAgIH1cbiAgfVxuXG4gIGZ1bmN0aW9uIHNjYWxlKHhhLCB5YSwgeGIsIHliLCBzLCBxKSB7XG4gICAgaWYgKHhhICE9PSB4YiB8fCB5YSAhPT0geWIpIHtcbiAgICAgIHZhciBpID0gcy5wdXNoKHBvcChzKSArIFwic2NhbGUoXCIsIG51bGwsIFwiLFwiLCBudWxsLCBcIilcIik7XG4gICAgICBxLnB1c2goe2k6IGkgLSA0LCB4OiBudW1iZXIoeGEsIHhiKX0sIHtpOiBpIC0gMiwgeDogbnVtYmVyKHlhLCB5Yil9KTtcbiAgICB9IGVsc2UgaWYgKHhiICE9PSAxIHx8IHliICE9PSAxKSB7XG4gICAgICBzLnB1c2gocG9wKHMpICsgXCJzY2FsZShcIiArIHhiICsgXCIsXCIgKyB5YiArIFwiKVwiKTtcbiAgICB9XG4gIH1cblxuICByZXR1cm4gZnVuY3Rpb24oYSwgYikge1xuICAgIHZhciBzID0gW10sIC8vIHN0cmluZyBjb25zdGFudHMgYW5kIHBsYWNlaG9sZGVyc1xuICAgICAgICBxID0gW107IC8vIG51bWJlciBpbnRlcnBvbGF0b3JzXG4gICAgYSA9IHBhcnNlKGEpLCBiID0gcGFyc2UoYik7XG4gICAgdHJhbnNsYXRlKGEudHJhbnNsYXRlWCwgYS50cmFuc2xhdGVZLCBiLnRyYW5zbGF0ZVgsIGIudHJhbnNsYXRlWSwgcywgcSk7XG4gICAgcm90YXRlKGEucm90YXRlLCBiLnJvdGF0ZSwgcywgcSk7XG4gICAgc2tld1goYS5za2V3WCwgYi5za2V3WCwgcywgcSk7XG4gICAgc2NhbGUoYS5zY2FsZVgsIGEuc2NhbGVZLCBiLnNjYWxlWCwgYi5zY2FsZVksIHMsIHEpO1xuICAgIGEgPSBiID0gbnVsbDsgLy8gZ2NcbiAgICByZXR1cm4gZnVuY3Rpb24odCkge1xuICAgICAgdmFyIGkgPSAtMSwgbiA9IHEubGVuZ3RoLCBvO1xuICAgICAgd2hpbGUgKCsraSA8IG4pIHNbKG8gPSBxW2ldKS5pXSA9IG8ueCh0KTtcbiAgICAgIHJldHVybiBzLmpvaW4oXCJcIik7XG4gICAgfTtcbiAgfTtcbn1cblxuZXhwb3J0IHZhciBpbnRlcnBvbGF0ZVRyYW5zZm9ybUNzcyA9IGludGVycG9sYXRlVHJhbnNmb3JtKHBhcnNlQ3NzLCBcInB4LCBcIiwgXCJweClcIiwgXCJkZWcpXCIpO1xuZXhwb3J0IHZhciBpbnRlcnBvbGF0ZVRyYW5zZm9ybVN2ZyA9IGludGVycG9sYXRlVHJhbnNmb3JtKHBhcnNlU3ZnLCBcIiwgXCIsIFwiKVwiLCBcIilcIik7XG4iLCJ2YXIgZXBzaWxvbjIgPSAxZS0xMjtcblxuZnVuY3Rpb24gY29zaCh4KSB7XG4gIHJldHVybiAoKHggPSBNYXRoLmV4cCh4KSkgKyAxIC8geCkgLyAyO1xufVxuXG5mdW5jdGlvbiBzaW5oKHgpIHtcbiAgcmV0dXJuICgoeCA9IE1hdGguZXhwKHgpKSAtIDEgLyB4KSAvIDI7XG59XG5cbmZ1bmN0aW9uIHRhbmgoeCkge1xuICByZXR1cm4gKCh4ID0gTWF0aC5leHAoMiAqIHgpKSAtIDEpIC8gKHggKyAxKTtcbn1cblxuZXhwb3J0IGRlZmF1bHQgKGZ1bmN0aW9uIHpvb21SaG8ocmhvLCByaG8yLCByaG80KSB7XG5cbiAgLy8gcDAgPSBbdXgwLCB1eTAsIHcwXVxuICAvLyBwMSA9IFt1eDEsIHV5MSwgdzFdXG4gIGZ1bmN0aW9uIHpvb20ocDAsIHAxKSB7XG4gICAgdmFyIHV4MCA9IHAwWzBdLCB1eTAgPSBwMFsxXSwgdzAgPSBwMFsyXSxcbiAgICAgICAgdXgxID0gcDFbMF0sIHV5MSA9IHAxWzFdLCB3MSA9IHAxWzJdLFxuICAgICAgICBkeCA9IHV4MSAtIHV4MCxcbiAgICAgICAgZHkgPSB1eTEgLSB1eTAsXG4gICAgICAgIGQyID0gZHggKiBkeCArIGR5ICogZHksXG4gICAgICAgIGksXG4gICAgICAgIFM7XG5cbiAgICAvLyBTcGVjaWFsIGNhc2UgZm9yIHUwIOKJhSB1MS5cbiAgICBpZiAoZDIgPCBlcHNpbG9uMikge1xuICAgICAgUyA9IE1hdGgubG9nKHcxIC8gdzApIC8gcmhvO1xuICAgICAgaSA9IGZ1bmN0aW9uKHQpIHtcbiAgICAgICAgcmV0dXJuIFtcbiAgICAgICAgICB1eDAgKyB0ICogZHgsXG4gICAgICAgICAgdXkwICsgdCAqIGR5LFxuICAgICAgICAgIHcwICogTWF0aC5leHAocmhvICogdCAqIFMpXG4gICAgICAgIF07XG4gICAgICB9XG4gICAgfVxuXG4gICAgLy8gR2VuZXJhbCBjYXNlLlxuICAgIGVsc2Uge1xuICAgICAgdmFyIGQxID0gTWF0aC5zcXJ0KGQyKSxcbiAgICAgICAgICBiMCA9ICh3MSAqIHcxIC0gdzAgKiB3MCArIHJobzQgKiBkMikgLyAoMiAqIHcwICogcmhvMiAqIGQxKSxcbiAgICAgICAgICBiMSA9ICh3MSAqIHcxIC0gdzAgKiB3MCAtIHJobzQgKiBkMikgLyAoMiAqIHcxICogcmhvMiAqIGQxKSxcbiAgICAgICAgICByMCA9IE1hdGgubG9nKE1hdGguc3FydChiMCAqIGIwICsgMSkgLSBiMCksXG4gICAgICAgICAgcjEgPSBNYXRoLmxvZyhNYXRoLnNxcnQoYjEgKiBiMSArIDEpIC0gYjEpO1xuICAgICAgUyA9IChyMSAtIHIwKSAvIHJobztcbiAgICAgIGkgPSBmdW5jdGlvbih0KSB7XG4gICAgICAgIHZhciBzID0gdCAqIFMsXG4gICAgICAgICAgICBjb3NocjAgPSBjb3NoKHIwKSxcbiAgICAgICAgICAgIHUgPSB3MCAvIChyaG8yICogZDEpICogKGNvc2hyMCAqIHRhbmgocmhvICogcyArIHIwKSAtIHNpbmgocjApKTtcbiAgICAgICAgcmV0dXJuIFtcbiAgICAgICAgICB1eDAgKyB1ICogZHgsXG4gICAgICAgICAgdXkwICsgdSAqIGR5LFxuICAgICAgICAgIHcwICogY29zaHIwIC8gY29zaChyaG8gKiBzICsgcjApXG4gICAgICAgIF07XG4gICAgICB9XG4gICAgfVxuXG4gICAgaS5kdXJhdGlvbiA9IFMgKiAxMDAwICogcmhvIC8gTWF0aC5TUVJUMjtcblxuICAgIHJldHVybiBpO1xuICB9XG5cbiAgem9vbS5yaG8gPSBmdW5jdGlvbihfKSB7XG4gICAgdmFyIF8xID0gTWF0aC5tYXgoMWUtMywgK18pLCBfMiA9IF8xICogXzEsIF80ID0gXzIgKiBfMjtcbiAgICByZXR1cm4gem9vbVJobyhfMSwgXzIsIF80KTtcbiAgfTtcblxuICByZXR1cm4gem9vbTtcbn0pKE1hdGguU1FSVDIsIDIsIDQpO1xuIiwidmFyIGZyYW1lID0gMCwgLy8gaXMgYW4gYW5pbWF0aW9uIGZyYW1lIHBlbmRpbmc/XG4gICAgdGltZW91dCA9IDAsIC8vIGlzIGEgdGltZW91dCBwZW5kaW5nP1xuICAgIGludGVydmFsID0gMCwgLy8gYXJlIGFueSB0aW1lcnMgYWN0aXZlP1xuICAgIHBva2VEZWxheSA9IDEwMDAsIC8vIGhvdyBmcmVxdWVudGx5IHdlIGNoZWNrIGZvciBjbG9jayBza2V3XG4gICAgdGFza0hlYWQsXG4gICAgdGFza1RhaWwsXG4gICAgY2xvY2tMYXN0ID0gMCxcbiAgICBjbG9ja05vdyA9IDAsXG4gICAgY2xvY2tTa2V3ID0gMCxcbiAgICBjbG9jayA9IHR5cGVvZiBwZXJmb3JtYW5jZSA9PT0gXCJvYmplY3RcIiAmJiBwZXJmb3JtYW5jZS5ub3cgPyBwZXJmb3JtYW5jZSA6IERhdGUsXG4gICAgc2V0RnJhbWUgPSB0eXBlb2Ygd2luZG93ID09PSBcIm9iamVjdFwiICYmIHdpbmRvdy5yZXF1ZXN0QW5pbWF0aW9uRnJhbWUgPyB3aW5kb3cucmVxdWVzdEFuaW1hdGlvbkZyYW1lLmJpbmQod2luZG93KSA6IGZ1bmN0aW9uKGYpIHsgc2V0VGltZW91dChmLCAxNyk7IH07XG5cbmV4cG9ydCBmdW5jdGlvbiBub3coKSB7XG4gIHJldHVybiBjbG9ja05vdyB8fCAoc2V0RnJhbWUoY2xlYXJOb3cpLCBjbG9ja05vdyA9IGNsb2NrLm5vdygpICsgY2xvY2tTa2V3KTtcbn1cblxuZnVuY3Rpb24gY2xlYXJOb3coKSB7XG4gIGNsb2NrTm93ID0gMDtcbn1cblxuZXhwb3J0IGZ1bmN0aW9uIFRpbWVyKCkge1xuICB0aGlzLl9jYWxsID1cbiAgdGhpcy5fdGltZSA9XG4gIHRoaXMuX25leHQgPSBudWxsO1xufVxuXG5UaW1lci5wcm90b3R5cGUgPSB0aW1lci5wcm90b3R5cGUgPSB7XG4gIGNvbnN0cnVjdG9yOiBUaW1lcixcbiAgcmVzdGFydDogZnVuY3Rpb24oY2FsbGJhY2ssIGRlbGF5LCB0aW1lKSB7XG4gICAgaWYgKHR5cGVvZiBjYWxsYmFjayAhPT0gXCJmdW5jdGlvblwiKSB0aHJvdyBuZXcgVHlwZUVycm9yKFwiY2FsbGJhY2sgaXMgbm90IGEgZnVuY3Rpb25cIik7XG4gICAgdGltZSA9ICh0aW1lID09IG51bGwgPyBub3coKSA6ICt0aW1lKSArIChkZWxheSA9PSBudWxsID8gMCA6ICtkZWxheSk7XG4gICAgaWYgKCF0aGlzLl9uZXh0ICYmIHRhc2tUYWlsICE9PSB0aGlzKSB7XG4gICAgICBpZiAodGFza1RhaWwpIHRhc2tUYWlsLl9uZXh0ID0gdGhpcztcbiAgICAgIGVsc2UgdGFza0hlYWQgPSB0aGlzO1xuICAgICAgdGFza1RhaWwgPSB0aGlzO1xuICAgIH1cbiAgICB0aGlzLl9jYWxsID0gY2FsbGJhY2s7XG4gICAgdGhpcy5fdGltZSA9IHRpbWU7XG4gICAgc2xlZXAoKTtcbiAgfSxcbiAgc3RvcDogZnVuY3Rpb24oKSB7XG4gICAgaWYgKHRoaXMuX2NhbGwpIHtcbiAgICAgIHRoaXMuX2NhbGwgPSBudWxsO1xuICAgICAgdGhpcy5fdGltZSA9IEluZmluaXR5O1xuICAgICAgc2xlZXAoKTtcbiAgICB9XG4gIH1cbn07XG5cbmV4cG9ydCBmdW5jdGlvbiB0aW1lcihjYWxsYmFjaywgZGVsYXksIHRpbWUpIHtcbiAgdmFyIHQgPSBuZXcgVGltZXI7XG4gIHQucmVzdGFydChjYWxsYmFjaywgZGVsYXksIHRpbWUpO1xuICByZXR1cm4gdDtcbn1cblxuZXhwb3J0IGZ1bmN0aW9uIHRpbWVyRmx1c2goKSB7XG4gIG5vdygpOyAvLyBHZXQgdGhlIGN1cnJlbnQgdGltZSwgaWYgbm90IGFscmVhZHkgc2V0LlxuICArK2ZyYW1lOyAvLyBQcmV0ZW5kIHdl4oCZdmUgc2V0IGFuIGFsYXJtLCBpZiB3ZSBoYXZlbuKAmXQgYWxyZWFkeS5cbiAgdmFyIHQgPSB0YXNrSGVhZCwgZTtcbiAgd2hpbGUgKHQpIHtcbiAgICBpZiAoKGUgPSBjbG9ja05vdyAtIHQuX3RpbWUpID49IDApIHQuX2NhbGwuY2FsbCh1bmRlZmluZWQsIGUpO1xuICAgIHQgPSB0Ll9uZXh0O1xuICB9XG4gIC0tZnJhbWU7XG59XG5cbmZ1bmN0aW9uIHdha2UoKSB7XG4gIGNsb2NrTm93ID0gKGNsb2NrTGFzdCA9IGNsb2NrLm5vdygpKSArIGNsb2NrU2tldztcbiAgZnJhbWUgPSB0aW1lb3V0ID0gMDtcbiAgdHJ5IHtcbiAgICB0aW1lckZsdXNoKCk7XG4gIH0gZmluYWxseSB7XG4gICAgZnJhbWUgPSAwO1xuICAgIG5hcCgpO1xuICAgIGNsb2NrTm93ID0gMDtcbiAgfVxufVxuXG5mdW5jdGlvbiBwb2tlKCkge1xuICB2YXIgbm93ID0gY2xvY2subm93KCksIGRlbGF5ID0gbm93IC0gY2xvY2tMYXN0O1xuICBpZiAoZGVsYXkgPiBwb2tlRGVsYXkpIGNsb2NrU2tldyAtPSBkZWxheSwgY2xvY2tMYXN0ID0gbm93O1xufVxuXG5mdW5jdGlvbiBuYXAoKSB7XG4gIHZhciB0MCwgdDEgPSB0YXNrSGVhZCwgdDIsIHRpbWUgPSBJbmZpbml0eTtcbiAgd2hpbGUgKHQxKSB7XG4gICAgaWYgKHQxLl9jYWxsKSB7XG4gICAgICBpZiAodGltZSA+IHQxLl90aW1lKSB0aW1lID0gdDEuX3RpbWU7XG4gICAgICB0MCA9IHQxLCB0MSA9IHQxLl9uZXh0O1xuICAgIH0gZWxzZSB7XG4gICAgICB0MiA9IHQxLl9uZXh0LCB0MS5fbmV4dCA9IG51bGw7XG4gICAgICB0MSA9IHQwID8gdDAuX25leHQgPSB0MiA6IHRhc2tIZWFkID0gdDI7XG4gICAgfVxuICB9XG4gIHRhc2tUYWlsID0gdDA7XG4gIHNsZWVwKHRpbWUpO1xufVxuXG5mdW5jdGlvbiBzbGVlcCh0aW1lKSB7XG4gIGlmIChmcmFtZSkgcmV0dXJuOyAvLyBTb29uZXN0IGFsYXJtIGFscmVhZHkgc2V0LCBvciB3aWxsIGJlLlxuICBpZiAodGltZW91dCkgdGltZW91dCA9IGNsZWFyVGltZW91dCh0aW1lb3V0KTtcbiAgdmFyIGRlbGF5ID0gdGltZSAtIGNsb2NrTm93OyAvLyBTdHJpY3RseSBsZXNzIHRoYW4gaWYgd2UgcmVjb21wdXRlZCBjbG9ja05vdy5cbiAgaWYgKGRlbGF5ID4gMjQpIHtcbiAgICBpZiAodGltZSA8IEluZmluaXR5KSB0aW1lb3V0ID0gc2V0VGltZW91dCh3YWtlLCB0aW1lIC0gY2xvY2subm93KCkgLSBjbG9ja1NrZXcpO1xuICAgIGlmIChpbnRlcnZhbCkgaW50ZXJ2YWwgPSBjbGVhckludGVydmFsKGludGVydmFsKTtcbiAgfSBlbHNlIHtcbiAgICBpZiAoIWludGVydmFsKSBjbG9ja0xhc3QgPSBjbG9jay5ub3coKSwgaW50ZXJ2YWwgPSBzZXRJbnRlcnZhbChwb2tlLCBwb2tlRGVsYXkpO1xuICAgIGZyYW1lID0gMSwgc2V0RnJhbWUod2FrZSk7XG4gIH1cbn1cbiIsImltcG9ydCB7VGltZXJ9IGZyb20gXCIuL3RpbWVyLmpzXCI7XG5cbmV4cG9ydCBkZWZhdWx0IGZ1bmN0aW9uKGNhbGxiYWNrLCBkZWxheSwgdGltZSkge1xuICB2YXIgdCA9IG5ldyBUaW1lcjtcbiAgZGVsYXkgPSBkZWxheSA9PSBudWxsID8gMCA6ICtkZWxheTtcbiAgdC5yZXN0YXJ0KGVsYXBzZWQgPT4ge1xuICAgIHQuc3RvcCgpO1xuICAgIGNhbGxiYWNrKGVsYXBzZWQgKyBkZWxheSk7XG4gIH0sIGRlbGF5LCB0aW1lKTtcbiAgcmV0dXJuIHQ7XG59XG4iLCJpbXBvcnQge2Rpc3BhdGNofSBmcm9tIFwiZDMtZGlzcGF0Y2hcIjtcbmltcG9ydCB7dGltZXIsIHRpbWVvdXR9IGZyb20gXCJkMy10aW1lclwiO1xuXG52YXIgZW1wdHlPbiA9IGRpc3BhdGNoKFwic3RhcnRcIiwgXCJlbmRcIiwgXCJjYW5jZWxcIiwgXCJpbnRlcnJ1cHRcIik7XG52YXIgZW1wdHlUd2VlbiA9IFtdO1xuXG5leHBvcnQgdmFyIENSRUFURUQgPSAwO1xuZXhwb3J0IHZhciBTQ0hFRFVMRUQgPSAxO1xuZXhwb3J0IHZhciBTVEFSVElORyA9IDI7XG5leHBvcnQgdmFyIFNUQVJURUQgPSAzO1xuZXhwb3J0IHZhciBSVU5OSU5HID0gNDtcbmV4cG9ydCB2YXIgRU5ESU5HID0gNTtcbmV4cG9ydCB2YXIgRU5ERUQgPSA2O1xuXG5leHBvcnQgZGVmYXVsdCBmdW5jdGlvbihub2RlLCBuYW1lLCBpZCwgaW5kZXgsIGdyb3VwLCB0aW1pbmcpIHtcbiAgdmFyIHNjaGVkdWxlcyA9IG5vZGUuX190cmFuc2l0aW9uO1xuICBpZiAoIXNjaGVkdWxlcykgbm9kZS5fX3RyYW5zaXRpb24gPSB7fTtcbiAgZWxzZSBpZiAoaWQgaW4gc2NoZWR1bGVzKSByZXR1cm47XG4gIGNyZWF0ZShub2RlLCBpZCwge1xuICAgIG5hbWU6IG5hbWUsXG4gICAgaW5kZXg6IGluZGV4LCAvLyBGb3IgY29udGV4dCBkdXJpbmcgY2FsbGJhY2suXG4gICAgZ3JvdXA6IGdyb3VwLCAvLyBGb3IgY29udGV4dCBkdXJpbmcgY2FsbGJhY2suXG4gICAgb246IGVtcHR5T24sXG4gICAgdHdlZW46IGVtcHR5VHdlZW4sXG4gICAgdGltZTogdGltaW5nLnRpbWUsXG4gICAgZGVsYXk6IHRpbWluZy5kZWxheSxcbiAgICBkdXJhdGlvbjogdGltaW5nLmR1cmF0aW9uLFxuICAgIGVhc2U6IHRpbWluZy5lYXNlLFxuICAgIHRpbWVyOiBudWxsLFxuICAgIHN0YXRlOiBDUkVBVEVEXG4gIH0pO1xufVxuXG5leHBvcnQgZnVuY3Rpb24gaW5pdChub2RlLCBpZCkge1xuICB2YXIgc2NoZWR1bGUgPSBnZXQobm9kZSwgaWQpO1xuICBpZiAoc2NoZWR1bGUuc3RhdGUgPiBDUkVBVEVEKSB0aHJvdyBuZXcgRXJyb3IoXCJ0b28gbGF0ZTsgYWxyZWFkeSBzY2hlZHVsZWRcIik7XG4gIHJldHVybiBzY2hlZHVsZTtcbn1cblxuZXhwb3J0IGZ1bmN0aW9uIHNldChub2RlLCBpZCkge1xuICB2YXIgc2NoZWR1bGUgPSBnZXQobm9kZSwgaWQpO1xuICBpZiAoc2NoZWR1bGUuc3RhdGUgPiBTVEFSVEVEKSB0aHJvdyBuZXcgRXJyb3IoXCJ0b28gbGF0ZTsgYWxyZWFkeSBydW5uaW5nXCIpO1xuICByZXR1cm4gc2NoZWR1bGU7XG59XG5cbmV4cG9ydCBmdW5jdGlvbiBnZXQobm9kZSwgaWQpIHtcbiAgdmFyIHNjaGVkdWxlID0gbm9kZS5fX3RyYW5zaXRpb247XG4gIGlmICghc2NoZWR1bGUgfHwgIShzY2hlZHVsZSA9IHNjaGVkdWxlW2lkXSkpIHRocm93IG5ldyBFcnJvcihcInRyYW5zaXRpb24gbm90IGZvdW5kXCIpO1xuICByZXR1cm4gc2NoZWR1bGU7XG59XG5cbmZ1bmN0aW9uIGNyZWF0ZShub2RlLCBpZCwgc2VsZikge1xuICB2YXIgc2NoZWR1bGVzID0gbm9kZS5fX3RyYW5zaXRpb24sXG4gICAgICB0d2VlbjtcblxuICAvLyBJbml0aWFsaXplIHRoZSBzZWxmIHRpbWVyIHdoZW4gdGhlIHRyYW5zaXRpb24gaXMgY3JlYXRlZC5cbiAgLy8gTm90ZSB0aGUgYWN0dWFsIGRlbGF5IGlzIG5vdCBrbm93biB1bnRpbCB0aGUgZmlyc3QgY2FsbGJhY2shXG4gIHNjaGVkdWxlc1tpZF0gPSBzZWxmO1xuICBzZWxmLnRpbWVyID0gdGltZXIoc2NoZWR1bGUsIDAsIHNlbGYudGltZSk7XG5cbiAgZnVuY3Rpb24gc2NoZWR1bGUoZWxhcHNlZCkge1xuICAgIHNlbGYuc3RhdGUgPSBTQ0hFRFVMRUQ7XG4gICAgc2VsZi50aW1lci5yZXN0YXJ0KHN0YXJ0LCBzZWxmLmRlbGF5LCBzZWxmLnRpbWUpO1xuXG4gICAgLy8gSWYgdGhlIGVsYXBzZWQgZGVsYXkgaXMgbGVzcyB0aGFuIG91ciBmaXJzdCBzbGVlcCwgc3RhcnQgaW1tZWRpYXRlbHkuXG4gICAgaWYgKHNlbGYuZGVsYXkgPD0gZWxhcHNlZCkgc3RhcnQoZWxhcHNlZCAtIHNlbGYuZGVsYXkpO1xuICB9XG5cbiAgZnVuY3Rpb24gc3RhcnQoZWxhcHNlZCkge1xuICAgIHZhciBpLCBqLCBuLCBvO1xuXG4gICAgLy8gSWYgdGhlIHN0YXRlIGlzIG5vdCBTQ0hFRFVMRUQsIHRoZW4gd2UgcHJldmlvdXNseSBlcnJvcmVkIG9uIHN0YXJ0LlxuICAgIGlmIChzZWxmLnN0YXRlICE9PSBTQ0hFRFVMRUQpIHJldHVybiBzdG9wKCk7XG5cbiAgICBmb3IgKGkgaW4gc2NoZWR1bGVzKSB7XG4gICAgICBvID0gc2NoZWR1bGVzW2ldO1xuICAgICAgaWYgKG8ubmFtZSAhPT0gc2VsZi5uYW1lKSBjb250aW51ZTtcblxuICAgICAgLy8gV2hpbGUgdGhpcyBlbGVtZW50IGFscmVhZHkgaGFzIGEgc3RhcnRpbmcgdHJhbnNpdGlvbiBkdXJpbmcgdGhpcyBmcmFtZSxcbiAgICAgIC8vIGRlZmVyIHN0YXJ0aW5nIGFuIGludGVycnVwdGluZyB0cmFuc2l0aW9uIHVudGlsIHRoYXQgdHJhbnNpdGlvbiBoYXMgYVxuICAgICAgLy8gY2hhbmNlIHRvIHRpY2sgKGFuZCBwb3NzaWJseSBlbmQpOyBzZWUgZDMvZDMtdHJhbnNpdGlvbiM1NCFcbiAgICAgIGlmIChvLnN0YXRlID09PSBTVEFSVEVEKSByZXR1cm4gdGltZW91dChzdGFydCk7XG5cbiAgICAgIC8vIEludGVycnVwdCB0aGUgYWN0aXZlIHRyYW5zaXRpb24sIGlmIGFueS5cbiAgICAgIGlmIChvLnN0YXRlID09PSBSVU5OSU5HKSB7XG4gICAgICAgIG8uc3RhdGUgPSBFTkRFRDtcbiAgICAgICAgby50aW1lci5zdG9wKCk7XG4gICAgICAgIG8ub24uY2FsbChcImludGVycnVwdFwiLCBub2RlLCBub2RlLl9fZGF0YV9fLCBvLmluZGV4LCBvLmdyb3VwKTtcbiAgICAgICAgZGVsZXRlIHNjaGVkdWxlc1tpXTtcbiAgICAgIH1cblxuICAgICAgLy8gQ2FuY2VsIGFueSBwcmUtZW1wdGVkIHRyYW5zaXRpb25zLlxuICAgICAgZWxzZSBpZiAoK2kgPCBpZCkge1xuICAgICAgICBvLnN0YXRlID0gRU5ERUQ7XG4gICAgICAgIG8udGltZXIuc3RvcCgpO1xuICAgICAgICBvLm9uLmNhbGwoXCJjYW5jZWxcIiwgbm9kZSwgbm9kZS5fX2RhdGFfXywgby5pbmRleCwgby5ncm91cCk7XG4gICAgICAgIGRlbGV0ZSBzY2hlZHVsZXNbaV07XG4gICAgICB9XG4gICAgfVxuXG4gICAgLy8gRGVmZXIgdGhlIGZpcnN0IHRpY2sgdG8gZW5kIG9mIHRoZSBjdXJyZW50IGZyYW1lOyBzZWUgZDMvZDMjMTU3Ni5cbiAgICAvLyBOb3RlIHRoZSB0cmFuc2l0aW9uIG1heSBiZSBjYW5jZWxlZCBhZnRlciBzdGFydCBhbmQgYmVmb3JlIHRoZSBmaXJzdCB0aWNrIVxuICAgIC8vIE5vdGUgdGhpcyBtdXN0IGJlIHNjaGVkdWxlZCBiZWZvcmUgdGhlIHN0YXJ0IGV2ZW50OyBzZWUgZDMvZDMtdHJhbnNpdGlvbiMxNiFcbiAgICAvLyBBc3N1bWluZyB0aGlzIGlzIHN1Y2Nlc3NmdWwsIHN1YnNlcXVlbnQgY2FsbGJhY2tzIGdvIHN0cmFpZ2h0IHRvIHRpY2suXG4gICAgdGltZW91dChmdW5jdGlvbigpIHtcbiAgICAgIGlmIChzZWxmLnN0YXRlID09PSBTVEFSVEVEKSB7XG4gICAgICAgIHNlbGYuc3RhdGUgPSBSVU5OSU5HO1xuICAgICAgICBzZWxmLnRpbWVyLnJlc3RhcnQodGljaywgc2VsZi5kZWxheSwgc2VsZi50aW1lKTtcbiAgICAgICAgdGljayhlbGFwc2VkKTtcbiAgICAgIH1cbiAgICB9KTtcblxuICAgIC8vIERpc3BhdGNoIHRoZSBzdGFydCBldmVudC5cbiAgICAvLyBOb3RlIHRoaXMgbXVzdCBiZSBkb25lIGJlZm9yZSB0aGUgdHdlZW4gYXJlIGluaXRpYWxpemVkLlxuICAgIHNlbGYuc3RhdGUgPSBTVEFSVElORztcbiAgICBzZWxmLm9uLmNhbGwoXCJzdGFydFwiLCBub2RlLCBub2RlLl9fZGF0YV9fLCBzZWxmLmluZGV4LCBzZWxmLmdyb3VwKTtcbiAgICBpZiAoc2VsZi5zdGF0ZSAhPT0gU1RBUlRJTkcpIHJldHVybjsgLy8gaW50ZXJydXB0ZWRcbiAgICBzZWxmLnN0YXRlID0gU1RBUlRFRDtcblxuICAgIC8vIEluaXRpYWxpemUgdGhlIHR3ZWVuLCBkZWxldGluZyBudWxsIHR3ZWVuLlxuICAgIHR3ZWVuID0gbmV3IEFycmF5KG4gPSBzZWxmLnR3ZWVuLmxlbmd0aCk7XG4gICAgZm9yIChpID0gMCwgaiA9IC0xOyBpIDwgbjsgKytpKSB7XG4gICAgICBpZiAobyA9IHNlbGYudHdlZW5baV0udmFsdWUuY2FsbChub2RlLCBub2RlLl9fZGF0YV9fLCBzZWxmLmluZGV4LCBzZWxmLmdyb3VwKSkge1xuICAgICAgICB0d2VlblsrK2pdID0gbztcbiAgICAgIH1cbiAgICB9XG4gICAgdHdlZW4ubGVuZ3RoID0gaiArIDE7XG4gIH1cblxuICBmdW5jdGlvbiB0aWNrKGVsYXBzZWQpIHtcbiAgICB2YXIgdCA9IGVsYXBzZWQgPCBzZWxmLmR1cmF0aW9uID8gc2VsZi5lYXNlLmNhbGwobnVsbCwgZWxhcHNlZCAvIHNlbGYuZHVyYXRpb24pIDogKHNlbGYudGltZXIucmVzdGFydChzdG9wKSwgc2VsZi5zdGF0ZSA9IEVORElORywgMSksXG4gICAgICAgIGkgPSAtMSxcbiAgICAgICAgbiA9IHR3ZWVuLmxlbmd0aDtcblxuICAgIHdoaWxlICgrK2kgPCBuKSB7XG4gICAgICB0d2VlbltpXS5jYWxsKG5vZGUsIHQpO1xuICAgIH1cblxuICAgIC8vIERpc3BhdGNoIHRoZSBlbmQgZXZlbnQuXG4gICAgaWYgKHNlbGYuc3RhdGUgPT09IEVORElORykge1xuICAgICAgc2VsZi5vbi5jYWxsKFwiZW5kXCIsIG5vZGUsIG5vZGUuX19kYXRhX18sIHNlbGYuaW5kZXgsIHNlbGYuZ3JvdXApO1xuICAgICAgc3RvcCgpO1xuICAgIH1cbiAgfVxuXG4gIGZ1bmN0aW9uIHN0b3AoKSB7XG4gICAgc2VsZi5zdGF0ZSA9IEVOREVEO1xuICAgIHNlbGYudGltZXIuc3RvcCgpO1xuICAgIGRlbGV0ZSBzY2hlZHVsZXNbaWRdO1xuICAgIGZvciAodmFyIGkgaW4gc2NoZWR1bGVzKSByZXR1cm47IC8vIGVzbGludC1kaXNhYmxlLWxpbmUgbm8tdW51c2VkLXZhcnNcbiAgICBkZWxldGUgbm9kZS5fX3RyYW5zaXRpb247XG4gIH1cbn1cbiIsImltcG9ydCB7U1RBUlRJTkcsIEVORElORywgRU5ERUR9IGZyb20gXCIuL3RyYW5zaXRpb24vc2NoZWR1bGUuanNcIjtcblxuZXhwb3J0IGRlZmF1bHQgZnVuY3Rpb24obm9kZSwgbmFtZSkge1xuICB2YXIgc2NoZWR1bGVzID0gbm9kZS5fX3RyYW5zaXRpb24sXG4gICAgICBzY2hlZHVsZSxcbiAgICAgIGFjdGl2ZSxcbiAgICAgIGVtcHR5ID0gdHJ1ZSxcbiAgICAgIGk7XG5cbiAgaWYgKCFzY2hlZHVsZXMpIHJldHVybjtcblxuICBuYW1lID0gbmFtZSA9PSBudWxsID8gbnVsbCA6IG5hbWUgKyBcIlwiO1xuXG4gIGZvciAoaSBpbiBzY2hlZHVsZXMpIHtcbiAgICBpZiAoKHNjaGVkdWxlID0gc2NoZWR1bGVzW2ldKS5uYW1lICE9PSBuYW1lKSB7IGVtcHR5ID0gZmFsc2U7IGNvbnRpbnVlOyB9XG4gICAgYWN0aXZlID0gc2NoZWR1bGUuc3RhdGUgPiBTVEFSVElORyAmJiBzY2hlZHVsZS5zdGF0ZSA8IEVORElORztcbiAgICBzY2hlZHVsZS5zdGF0ZSA9IEVOREVEO1xuICAgIHNjaGVkdWxlLnRpbWVyLnN0b3AoKTtcbiAgICBzY2hlZHVsZS5vbi5jYWxsKGFjdGl2ZSA/IFwiaW50ZXJydXB0XCIgOiBcImNhbmNlbFwiLCBub2RlLCBub2RlLl9fZGF0YV9fLCBzY2hlZHVsZS5pbmRleCwgc2NoZWR1bGUuZ3JvdXApO1xuICAgIGRlbGV0ZSBzY2hlZHVsZXNbaV07XG4gIH1cblxuICBpZiAoZW1wdHkpIGRlbGV0ZSBub2RlLl9fdHJhbnNpdGlvbjtcbn1cbiIsImltcG9ydCBpbnRlcnJ1cHQgZnJvbSBcIi4uL2ludGVycnVwdC5qc1wiO1xuXG5leHBvcnQgZGVmYXVsdCBmdW5jdGlvbihuYW1lKSB7XG4gIHJldHVybiB0aGlzLmVhY2goZnVuY3Rpb24oKSB7XG4gICAgaW50ZXJydXB0KHRoaXMsIG5hbWUpO1xuICB9KTtcbn1cbiIsImltcG9ydCB7Z2V0LCBzZXR9IGZyb20gXCIuL3NjaGVkdWxlLmpzXCI7XG5cbmZ1bmN0aW9uIHR3ZWVuUmVtb3ZlKGlkLCBuYW1lKSB7XG4gIHZhciB0d2VlbjAsIHR3ZWVuMTtcbiAgcmV0dXJuIGZ1bmN0aW9uKCkge1xuICAgIHZhciBzY2hlZHVsZSA9IHNldCh0aGlzLCBpZCksXG4gICAgICAgIHR3ZWVuID0gc2NoZWR1bGUudHdlZW47XG5cbiAgICAvLyBJZiB0aGlzIG5vZGUgc2hhcmVkIHR3ZWVuIHdpdGggdGhlIHByZXZpb3VzIG5vZGUsXG4gICAgLy8ganVzdCBhc3NpZ24gdGhlIHVwZGF0ZWQgc2hhcmVkIHR3ZWVuIGFuZCB3ZeKAmXJlIGRvbmUhXG4gICAgLy8gT3RoZXJ3aXNlLCBjb3B5LW9uLXdyaXRlLlxuICAgIGlmICh0d2VlbiAhPT0gdHdlZW4wKSB7XG4gICAgICB0d2VlbjEgPSB0d2VlbjAgPSB0d2VlbjtcbiAgICAgIGZvciAodmFyIGkgPSAwLCBuID0gdHdlZW4xLmxlbmd0aDsgaSA8IG47ICsraSkge1xuICAgICAgICBpZiAodHdlZW4xW2ldLm5hbWUgPT09IG5hbWUpIHtcbiAgICAgICAgICB0d2VlbjEgPSB0d2VlbjEuc2xpY2UoKTtcbiAgICAgICAgICB0d2VlbjEuc3BsaWNlKGksIDEpO1xuICAgICAgICAgIGJyZWFrO1xuICAgICAgICB9XG4gICAgICB9XG4gICAgfVxuXG4gICAgc2NoZWR1bGUudHdlZW4gPSB0d2VlbjE7XG4gIH07XG59XG5cbmZ1bmN0aW9uIHR3ZWVuRnVuY3Rpb24oaWQsIG5hbWUsIHZhbHVlKSB7XG4gIHZhciB0d2VlbjAsIHR3ZWVuMTtcbiAgaWYgKHR5cGVvZiB2YWx1ZSAhPT0gXCJmdW5jdGlvblwiKSB0aHJvdyBuZXcgRXJyb3I7XG4gIHJldHVybiBmdW5jdGlvbigpIHtcbiAgICB2YXIgc2NoZWR1bGUgPSBzZXQodGhpcywgaWQpLFxuICAgICAgICB0d2VlbiA9IHNjaGVkdWxlLnR3ZWVuO1xuXG4gICAgLy8gSWYgdGhpcyBub2RlIHNoYXJlZCB0d2VlbiB3aXRoIHRoZSBwcmV2aW91cyBub2RlLFxuICAgIC8vIGp1c3QgYXNzaWduIHRoZSB1cGRhdGVkIHNoYXJlZCB0d2VlbiBhbmQgd2XigJlyZSBkb25lIVxuICAgIC8vIE90aGVyd2lzZSwgY29weS1vbi13cml0ZS5cbiAgICBpZiAodHdlZW4gIT09IHR3ZWVuMCkge1xuICAgICAgdHdlZW4xID0gKHR3ZWVuMCA9IHR3ZWVuKS5zbGljZSgpO1xuICAgICAgZm9yICh2YXIgdCA9IHtuYW1lOiBuYW1lLCB2YWx1ZTogdmFsdWV9LCBpID0gMCwgbiA9IHR3ZWVuMS5sZW5ndGg7IGkgPCBuOyArK2kpIHtcbiAgICAgICAgaWYgKHR3ZWVuMVtpXS5uYW1lID09PSBuYW1lKSB7XG4gICAgICAgICAgdHdlZW4xW2ldID0gdDtcbiAgICAgICAgICBicmVhaztcbiAgICAgICAgfVxuICAgICAgfVxuICAgICAgaWYgKGkgPT09IG4pIHR3ZWVuMS5wdXNoKHQpO1xuICAgIH1cblxuICAgIHNjaGVkdWxlLnR3ZWVuID0gdHdlZW4xO1xuICB9O1xufVxuXG5leHBvcnQgZGVmYXVsdCBmdW5jdGlvbihuYW1lLCB2YWx1ZSkge1xuICB2YXIgaWQgPSB0aGlzLl9pZDtcblxuICBuYW1lICs9IFwiXCI7XG5cbiAgaWYgKGFyZ3VtZW50cy5sZW5ndGggPCAyKSB7XG4gICAgdmFyIHR3ZWVuID0gZ2V0KHRoaXMubm9kZSgpLCBpZCkudHdlZW47XG4gICAgZm9yICh2YXIgaSA9IDAsIG4gPSB0d2Vlbi5sZW5ndGgsIHQ7IGkgPCBuOyArK2kpIHtcbiAgICAgIGlmICgodCA9IHR3ZWVuW2ldKS5uYW1lID09PSBuYW1lKSB7XG4gICAgICAgIHJldHVybiB0LnZhbHVlO1xuICAgICAgfVxuICAgIH1cbiAgICByZXR1cm4gbnVsbDtcbiAgfVxuXG4gIHJldHVybiB0aGlzLmVhY2goKHZhbHVlID09IG51bGwgPyB0d2VlblJlbW92ZSA6IHR3ZWVuRnVuY3Rpb24pKGlkLCBuYW1lLCB2YWx1ZSkpO1xufVxuXG5leHBvcnQgZnVuY3Rpb24gdHdlZW5WYWx1ZSh0cmFuc2l0aW9uLCBuYW1lLCB2YWx1ZSkge1xuICB2YXIgaWQgPSB0cmFuc2l0aW9uLl9pZDtcblxuICB0cmFuc2l0aW9uLmVhY2goZnVuY3Rpb24oKSB7XG4gICAgdmFyIHNjaGVkdWxlID0gc2V0KHRoaXMsIGlkKTtcbiAgICAoc2NoZWR1bGUudmFsdWUgfHwgKHNjaGVkdWxlLnZhbHVlID0ge30pKVtuYW1lXSA9IHZhbHVlLmFwcGx5KHRoaXMsIGFyZ3VtZW50cyk7XG4gIH0pO1xuXG4gIHJldHVybiBmdW5jdGlvbihub2RlKSB7XG4gICAgcmV0dXJuIGdldChub2RlLCBpZCkudmFsdWVbbmFtZV07XG4gIH07XG59XG4iLCJpbXBvcnQge2NvbG9yfSBmcm9tIFwiZDMtY29sb3JcIjtcbmltcG9ydCB7aW50ZXJwb2xhdGVOdW1iZXIsIGludGVycG9sYXRlUmdiLCBpbnRlcnBvbGF0ZVN0cmluZ30gZnJvbSBcImQzLWludGVycG9sYXRlXCI7XG5cbmV4cG9ydCBkZWZhdWx0IGZ1bmN0aW9uKGEsIGIpIHtcbiAgdmFyIGM7XG4gIHJldHVybiAodHlwZW9mIGIgPT09IFwibnVtYmVyXCIgPyBpbnRlcnBvbGF0ZU51bWJlclxuICAgICAgOiBiIGluc3RhbmNlb2YgY29sb3IgPyBpbnRlcnBvbGF0ZVJnYlxuICAgICAgOiAoYyA9IGNvbG9yKGIpKSA/IChiID0gYywgaW50ZXJwb2xhdGVSZ2IpXG4gICAgICA6IGludGVycG9sYXRlU3RyaW5nKShhLCBiKTtcbn1cbiIsImltcG9ydCB7aW50ZXJwb2xhdGVUcmFuc2Zvcm1TdmcgYXMgaW50ZXJwb2xhdGVUcmFuc2Zvcm19IGZyb20gXCJkMy1pbnRlcnBvbGF0ZVwiO1xuaW1wb3J0IHtuYW1lc3BhY2V9IGZyb20gXCJkMy1zZWxlY3Rpb25cIjtcbmltcG9ydCB7dHdlZW5WYWx1ZX0gZnJvbSBcIi4vdHdlZW4uanNcIjtcbmltcG9ydCBpbnRlcnBvbGF0ZSBmcm9tIFwiLi9pbnRlcnBvbGF0ZS5qc1wiO1xuXG5mdW5jdGlvbiBhdHRyUmVtb3ZlKG5hbWUpIHtcbiAgcmV0dXJuIGZ1bmN0aW9uKCkge1xuICAgIHRoaXMucmVtb3ZlQXR0cmlidXRlKG5hbWUpO1xuICB9O1xufVxuXG5mdW5jdGlvbiBhdHRyUmVtb3ZlTlMoZnVsbG5hbWUpIHtcbiAgcmV0dXJuIGZ1bmN0aW9uKCkge1xuICAgIHRoaXMucmVtb3ZlQXR0cmlidXRlTlMoZnVsbG5hbWUuc3BhY2UsIGZ1bGxuYW1lLmxvY2FsKTtcbiAgfTtcbn1cblxuZnVuY3Rpb24gYXR0ckNvbnN0YW50KG5hbWUsIGludGVycG9sYXRlLCB2YWx1ZTEpIHtcbiAgdmFyIHN0cmluZzAwLFxuICAgICAgc3RyaW5nMSA9IHZhbHVlMSArIFwiXCIsXG4gICAgICBpbnRlcnBvbGF0ZTA7XG4gIHJldHVybiBmdW5jdGlvbigpIHtcbiAgICB2YXIgc3RyaW5nMCA9IHRoaXMuZ2V0QXR0cmlidXRlKG5hbWUpO1xuICAgIHJldHVybiBzdHJpbmcwID09PSBzdHJpbmcxID8gbnVsbFxuICAgICAgICA6IHN0cmluZzAgPT09IHN0cmluZzAwID8gaW50ZXJwb2xhdGUwXG4gICAgICAgIDogaW50ZXJwb2xhdGUwID0gaW50ZXJwb2xhdGUoc3RyaW5nMDAgPSBzdHJpbmcwLCB2YWx1ZTEpO1xuICB9O1xufVxuXG5mdW5jdGlvbiBhdHRyQ29uc3RhbnROUyhmdWxsbmFtZSwgaW50ZXJwb2xhdGUsIHZhbHVlMSkge1xuICB2YXIgc3RyaW5nMDAsXG4gICAgICBzdHJpbmcxID0gdmFsdWUxICsgXCJcIixcbiAgICAgIGludGVycG9sYXRlMDtcbiAgcmV0dXJuIGZ1bmN0aW9uKCkge1xuICAgIHZhciBzdHJpbmcwID0gdGhpcy5nZXRBdHRyaWJ1dGVOUyhmdWxsbmFtZS5zcGFjZSwgZnVsbG5hbWUubG9jYWwpO1xuICAgIHJldHVybiBzdHJpbmcwID09PSBzdHJpbmcxID8gbnVsbFxuICAgICAgICA6IHN0cmluZzAgPT09IHN0cmluZzAwID8gaW50ZXJwb2xhdGUwXG4gICAgICAgIDogaW50ZXJwb2xhdGUwID0gaW50ZXJwb2xhdGUoc3RyaW5nMDAgPSBzdHJpbmcwLCB2YWx1ZTEpO1xuICB9O1xufVxuXG5mdW5jdGlvbiBhdHRyRnVuY3Rpb24obmFtZSwgaW50ZXJwb2xhdGUsIHZhbHVlKSB7XG4gIHZhciBzdHJpbmcwMCxcbiAgICAgIHN0cmluZzEwLFxuICAgICAgaW50ZXJwb2xhdGUwO1xuICByZXR1cm4gZnVuY3Rpb24oKSB7XG4gICAgdmFyIHN0cmluZzAsIHZhbHVlMSA9IHZhbHVlKHRoaXMpLCBzdHJpbmcxO1xuICAgIGlmICh2YWx1ZTEgPT0gbnVsbCkgcmV0dXJuIHZvaWQgdGhpcy5yZW1vdmVBdHRyaWJ1dGUobmFtZSk7XG4gICAgc3RyaW5nMCA9IHRoaXMuZ2V0QXR0cmlidXRlKG5hbWUpO1xuICAgIHN0cmluZzEgPSB2YWx1ZTEgKyBcIlwiO1xuICAgIHJldHVybiBzdHJpbmcwID09PSBzdHJpbmcxID8gbnVsbFxuICAgICAgICA6IHN0cmluZzAgPT09IHN0cmluZzAwICYmIHN0cmluZzEgPT09IHN0cmluZzEwID8gaW50ZXJwb2xhdGUwXG4gICAgICAgIDogKHN0cmluZzEwID0gc3RyaW5nMSwgaW50ZXJwb2xhdGUwID0gaW50ZXJwb2xhdGUoc3RyaW5nMDAgPSBzdHJpbmcwLCB2YWx1ZTEpKTtcbiAgfTtcbn1cblxuZnVuY3Rpb24gYXR0ckZ1bmN0aW9uTlMoZnVsbG5hbWUsIGludGVycG9sYXRlLCB2YWx1ZSkge1xuICB2YXIgc3RyaW5nMDAsXG4gICAgICBzdHJpbmcxMCxcbiAgICAgIGludGVycG9sYXRlMDtcbiAgcmV0dXJuIGZ1bmN0aW9uKCkge1xuICAgIHZhciBzdHJpbmcwLCB2YWx1ZTEgPSB2YWx1ZSh0aGlzKSwgc3RyaW5nMTtcbiAgICBpZiAodmFsdWUxID09IG51bGwpIHJldHVybiB2b2lkIHRoaXMucmVtb3ZlQXR0cmlidXRlTlMoZnVsbG5hbWUuc3BhY2UsIGZ1bGxuYW1lLmxvY2FsKTtcbiAgICBzdHJpbmcwID0gdGhpcy5nZXRBdHRyaWJ1dGVOUyhmdWxsbmFtZS5zcGFjZSwgZnVsbG5hbWUubG9jYWwpO1xuICAgIHN0cmluZzEgPSB2YWx1ZTEgKyBcIlwiO1xuICAgIHJldHVybiBzdHJpbmcwID09PSBzdHJpbmcxID8gbnVsbFxuICAgICAgICA6IHN0cmluZzAgPT09IHN0cmluZzAwICYmIHN0cmluZzEgPT09IHN0cmluZzEwID8gaW50ZXJwb2xhdGUwXG4gICAgICAgIDogKHN0cmluZzEwID0gc3RyaW5nMSwgaW50ZXJwb2xhdGUwID0gaW50ZXJwb2xhdGUoc3RyaW5nMDAgPSBzdHJpbmcwLCB2YWx1ZTEpKTtcbiAgfTtcbn1cblxuZXhwb3J0IGRlZmF1bHQgZnVuY3Rpb24obmFtZSwgdmFsdWUpIHtcbiAgdmFyIGZ1bGxuYW1lID0gbmFtZXNwYWNlKG5hbWUpLCBpID0gZnVsbG5hbWUgPT09IFwidHJhbnNmb3JtXCIgPyBpbnRlcnBvbGF0ZVRyYW5zZm9ybSA6IGludGVycG9sYXRlO1xuICByZXR1cm4gdGhpcy5hdHRyVHdlZW4obmFtZSwgdHlwZW9mIHZhbHVlID09PSBcImZ1bmN0aW9uXCJcbiAgICAgID8gKGZ1bGxuYW1lLmxvY2FsID8gYXR0ckZ1bmN0aW9uTlMgOiBhdHRyRnVuY3Rpb24pKGZ1bGxuYW1lLCBpLCB0d2VlblZhbHVlKHRoaXMsIFwiYXR0ci5cIiArIG5hbWUsIHZhbHVlKSlcbiAgICAgIDogdmFsdWUgPT0gbnVsbCA/IChmdWxsbmFtZS5sb2NhbCA/IGF0dHJSZW1vdmVOUyA6IGF0dHJSZW1vdmUpKGZ1bGxuYW1lKVxuICAgICAgOiAoZnVsbG5hbWUubG9jYWwgPyBhdHRyQ29uc3RhbnROUyA6IGF0dHJDb25zdGFudCkoZnVsbG5hbWUsIGksIHZhbHVlKSk7XG59XG4iLCJpbXBvcnQge25hbWVzcGFjZX0gZnJvbSBcImQzLXNlbGVjdGlvblwiO1xuXG5mdW5jdGlvbiBhdHRySW50ZXJwb2xhdGUobmFtZSwgaSkge1xuICByZXR1cm4gZnVuY3Rpb24odCkge1xuICAgIHRoaXMuc2V0QXR0cmlidXRlKG5hbWUsIGkuY2FsbCh0aGlzLCB0KSk7XG4gIH07XG59XG5cbmZ1bmN0aW9uIGF0dHJJbnRlcnBvbGF0ZU5TKGZ1bGxuYW1lLCBpKSB7XG4gIHJldHVybiBmdW5jdGlvbih0KSB7XG4gICAgdGhpcy5zZXRBdHRyaWJ1dGVOUyhmdWxsbmFtZS5zcGFjZSwgZnVsbG5hbWUubG9jYWwsIGkuY2FsbCh0aGlzLCB0KSk7XG4gIH07XG59XG5cbmZ1bmN0aW9uIGF0dHJUd2Vlbk5TKGZ1bGxuYW1lLCB2YWx1ZSkge1xuICB2YXIgdDAsIGkwO1xuICBmdW5jdGlvbiB0d2VlbigpIHtcbiAgICB2YXIgaSA9IHZhbHVlLmFwcGx5KHRoaXMsIGFyZ3VtZW50cyk7XG4gICAgaWYgKGkgIT09IGkwKSB0MCA9IChpMCA9IGkpICYmIGF0dHJJbnRlcnBvbGF0ZU5TKGZ1bGxuYW1lLCBpKTtcbiAgICByZXR1cm4gdDA7XG4gIH1cbiAgdHdlZW4uX3ZhbHVlID0gdmFsdWU7XG4gIHJldHVybiB0d2Vlbjtcbn1cblxuZnVuY3Rpb24gYXR0clR3ZWVuKG5hbWUsIHZhbHVlKSB7XG4gIHZhciB0MCwgaTA7XG4gIGZ1bmN0aW9uIHR3ZWVuKCkge1xuICAgIHZhciBpID0gdmFsdWUuYXBwbHkodGhpcywgYXJndW1lbnRzKTtcbiAgICBpZiAoaSAhPT0gaTApIHQwID0gKGkwID0gaSkgJiYgYXR0ckludGVycG9sYXRlKG5hbWUsIGkpO1xuICAgIHJldHVybiB0MDtcbiAgfVxuICB0d2Vlbi5fdmFsdWUgPSB2YWx1ZTtcbiAgcmV0dXJuIHR3ZWVuO1xufVxuXG5leHBvcnQgZGVmYXVsdCBmdW5jdGlvbihuYW1lLCB2YWx1ZSkge1xuICB2YXIga2V5ID0gXCJhdHRyLlwiICsgbmFtZTtcbiAgaWYgKGFyZ3VtZW50cy5sZW5ndGggPCAyKSByZXR1cm4gKGtleSA9IHRoaXMudHdlZW4oa2V5KSkgJiYga2V5Ll92YWx1ZTtcbiAgaWYgKHZhbHVlID09IG51bGwpIHJldHVybiB0aGlzLnR3ZWVuKGtleSwgbnVsbCk7XG4gIGlmICh0eXBlb2YgdmFsdWUgIT09IFwiZnVuY3Rpb25cIikgdGhyb3cgbmV3IEVycm9yO1xuICB2YXIgZnVsbG5hbWUgPSBuYW1lc3BhY2UobmFtZSk7XG4gIHJldHVybiB0aGlzLnR3ZWVuKGtleSwgKGZ1bGxuYW1lLmxvY2FsID8gYXR0clR3ZWVuTlMgOiBhdHRyVHdlZW4pKGZ1bGxuYW1lLCB2YWx1ZSkpO1xufVxuIiwiaW1wb3J0IHtnZXQsIGluaXR9IGZyb20gXCIuL3NjaGVkdWxlLmpzXCI7XG5cbmZ1bmN0aW9uIGRlbGF5RnVuY3Rpb24oaWQsIHZhbHVlKSB7XG4gIHJldHVybiBmdW5jdGlvbigpIHtcbiAgICBpbml0KHRoaXMsIGlkKS5kZWxheSA9ICt2YWx1ZS5hcHBseSh0aGlzLCBhcmd1bWVudHMpO1xuICB9O1xufVxuXG5mdW5jdGlvbiBkZWxheUNvbnN0YW50KGlkLCB2YWx1ZSkge1xuICByZXR1cm4gdmFsdWUgPSArdmFsdWUsIGZ1bmN0aW9uKCkge1xuICAgIGluaXQodGhpcywgaWQpLmRlbGF5ID0gdmFsdWU7XG4gIH07XG59XG5cbmV4cG9ydCBkZWZhdWx0IGZ1bmN0aW9uKHZhbHVlKSB7XG4gIHZhciBpZCA9IHRoaXMuX2lkO1xuXG4gIHJldHVybiBhcmd1bWVudHMubGVuZ3RoXG4gICAgICA/IHRoaXMuZWFjaCgodHlwZW9mIHZhbHVlID09PSBcImZ1bmN0aW9uXCJcbiAgICAgICAgICA/IGRlbGF5RnVuY3Rpb25cbiAgICAgICAgICA6IGRlbGF5Q29uc3RhbnQpKGlkLCB2YWx1ZSkpXG4gICAgICA6IGdldCh0aGlzLm5vZGUoKSwgaWQpLmRlbGF5O1xufVxuIiwiaW1wb3J0IHtnZXQsIHNldH0gZnJvbSBcIi4vc2NoZWR1bGUuanNcIjtcblxuZnVuY3Rpb24gZHVyYXRpb25GdW5jdGlvbihpZCwgdmFsdWUpIHtcbiAgcmV0dXJuIGZ1bmN0aW9uKCkge1xuICAgIHNldCh0aGlzLCBpZCkuZHVyYXRpb24gPSArdmFsdWUuYXBwbHkodGhpcywgYXJndW1lbnRzKTtcbiAgfTtcbn1cblxuZnVuY3Rpb24gZHVyYXRpb25Db25zdGFudChpZCwgdmFsdWUpIHtcbiAgcmV0dXJuIHZhbHVlID0gK3ZhbHVlLCBmdW5jdGlvbigpIHtcbiAgICBzZXQodGhpcywgaWQpLmR1cmF0aW9uID0gdmFsdWU7XG4gIH07XG59XG5cbmV4cG9ydCBkZWZhdWx0IGZ1bmN0aW9uKHZhbHVlKSB7XG4gIHZhciBpZCA9IHRoaXMuX2lkO1xuXG4gIHJldHVybiBhcmd1bWVudHMubGVuZ3RoXG4gICAgICA/IHRoaXMuZWFjaCgodHlwZW9mIHZhbHVlID09PSBcImZ1bmN0aW9uXCJcbiAgICAgICAgICA/IGR1cmF0aW9uRnVuY3Rpb25cbiAgICAgICAgICA6IGR1cmF0aW9uQ29uc3RhbnQpKGlkLCB2YWx1ZSkpXG4gICAgICA6IGdldCh0aGlzLm5vZGUoKSwgaWQpLmR1cmF0aW9uO1xufVxuIiwiaW1wb3J0IHtnZXQsIHNldH0gZnJvbSBcIi4vc2NoZWR1bGUuanNcIjtcblxuZnVuY3Rpb24gZWFzZUNvbnN0YW50KGlkLCB2YWx1ZSkge1xuICBpZiAodHlwZW9mIHZhbHVlICE9PSBcImZ1bmN0aW9uXCIpIHRocm93IG5ldyBFcnJvcjtcbiAgcmV0dXJuIGZ1bmN0aW9uKCkge1xuICAgIHNldCh0aGlzLCBpZCkuZWFzZSA9IHZhbHVlO1xuICB9O1xufVxuXG5leHBvcnQgZGVmYXVsdCBmdW5jdGlvbih2YWx1ZSkge1xuICB2YXIgaWQgPSB0aGlzLl9pZDtcblxuICByZXR1cm4gYXJndW1lbnRzLmxlbmd0aFxuICAgICAgPyB0aGlzLmVhY2goZWFzZUNvbnN0YW50KGlkLCB2YWx1ZSkpXG4gICAgICA6IGdldCh0aGlzLm5vZGUoKSwgaWQpLmVhc2U7XG59XG4iLCJpbXBvcnQge3NldH0gZnJvbSBcIi4vc2NoZWR1bGUuanNcIjtcblxuZnVuY3Rpb24gZWFzZVZhcnlpbmcoaWQsIHZhbHVlKSB7XG4gIHJldHVybiBmdW5jdGlvbigpIHtcbiAgICB2YXIgdiA9IHZhbHVlLmFwcGx5KHRoaXMsIGFyZ3VtZW50cyk7XG4gICAgaWYgKHR5cGVvZiB2ICE9PSBcImZ1bmN0aW9uXCIpIHRocm93IG5ldyBFcnJvcjtcbiAgICBzZXQodGhpcywgaWQpLmVhc2UgPSB2O1xuICB9O1xufVxuXG5leHBvcnQgZGVmYXVsdCBmdW5jdGlvbih2YWx1ZSkge1xuICBpZiAodHlwZW9mIHZhbHVlICE9PSBcImZ1bmN0aW9uXCIpIHRocm93IG5ldyBFcnJvcjtcbiAgcmV0dXJuIHRoaXMuZWFjaChlYXNlVmFyeWluZyh0aGlzLl9pZCwgdmFsdWUpKTtcbn1cbiIsImltcG9ydCB7bWF0Y2hlcn0gZnJvbSBcImQzLXNlbGVjdGlvblwiO1xuaW1wb3J0IHtUcmFuc2l0aW9ufSBmcm9tIFwiLi9pbmRleC5qc1wiO1xuXG5leHBvcnQgZGVmYXVsdCBmdW5jdGlvbihtYXRjaCkge1xuICBpZiAodHlwZW9mIG1hdGNoICE9PSBcImZ1bmN0aW9uXCIpIG1hdGNoID0gbWF0Y2hlcihtYXRjaCk7XG5cbiAgZm9yICh2YXIgZ3JvdXBzID0gdGhpcy5fZ3JvdXBzLCBtID0gZ3JvdXBzLmxlbmd0aCwgc3ViZ3JvdXBzID0gbmV3IEFycmF5KG0pLCBqID0gMDsgaiA8IG07ICsraikge1xuICAgIGZvciAodmFyIGdyb3VwID0gZ3JvdXBzW2pdLCBuID0gZ3JvdXAubGVuZ3RoLCBzdWJncm91cCA9IHN1Ymdyb3Vwc1tqXSA9IFtdLCBub2RlLCBpID0gMDsgaSA8IG47ICsraSkge1xuICAgICAgaWYgKChub2RlID0gZ3JvdXBbaV0pICYmIG1hdGNoLmNhbGwobm9kZSwgbm9kZS5fX2RhdGFfXywgaSwgZ3JvdXApKSB7XG4gICAgICAgIHN1Ymdyb3VwLnB1c2gobm9kZSk7XG4gICAgICB9XG4gICAgfVxuICB9XG5cbiAgcmV0dXJuIG5ldyBUcmFuc2l0aW9uKHN1Ymdyb3VwcywgdGhpcy5fcGFyZW50cywgdGhpcy5fbmFtZSwgdGhpcy5faWQpO1xufVxuIiwiaW1wb3J0IHtUcmFuc2l0aW9ufSBmcm9tIFwiLi9pbmRleC5qc1wiO1xuXG5leHBvcnQgZGVmYXVsdCBmdW5jdGlvbih0cmFuc2l0aW9uKSB7XG4gIGlmICh0cmFuc2l0aW9uLl9pZCAhPT0gdGhpcy5faWQpIHRocm93IG5ldyBFcnJvcjtcblxuICBmb3IgKHZhciBncm91cHMwID0gdGhpcy5fZ3JvdXBzLCBncm91cHMxID0gdHJhbnNpdGlvbi5fZ3JvdXBzLCBtMCA9IGdyb3VwczAubGVuZ3RoLCBtMSA9IGdyb3VwczEubGVuZ3RoLCBtID0gTWF0aC5taW4obTAsIG0xKSwgbWVyZ2VzID0gbmV3IEFycmF5KG0wKSwgaiA9IDA7IGogPCBtOyArK2opIHtcbiAgICBmb3IgKHZhciBncm91cDAgPSBncm91cHMwW2pdLCBncm91cDEgPSBncm91cHMxW2pdLCBuID0gZ3JvdXAwLmxlbmd0aCwgbWVyZ2UgPSBtZXJnZXNbal0gPSBuZXcgQXJyYXkobiksIG5vZGUsIGkgPSAwOyBpIDwgbjsgKytpKSB7XG4gICAgICBpZiAobm9kZSA9IGdyb3VwMFtpXSB8fCBncm91cDFbaV0pIHtcbiAgICAgICAgbWVyZ2VbaV0gPSBub2RlO1xuICAgICAgfVxuICAgIH1cbiAgfVxuXG4gIGZvciAoOyBqIDwgbTA7ICsraikge1xuICAgIG1lcmdlc1tqXSA9IGdyb3VwczBbal07XG4gIH1cblxuICByZXR1cm4gbmV3IFRyYW5zaXRpb24obWVyZ2VzLCB0aGlzLl9wYXJlbnRzLCB0aGlzLl9uYW1lLCB0aGlzLl9pZCk7XG59XG4iLCJpbXBvcnQge2dldCwgc2V0LCBpbml0fSBmcm9tIFwiLi9zY2hlZHVsZS5qc1wiO1xuXG5mdW5jdGlvbiBzdGFydChuYW1lKSB7XG4gIHJldHVybiAobmFtZSArIFwiXCIpLnRyaW0oKS5zcGxpdCgvXnxcXHMrLykuZXZlcnkoZnVuY3Rpb24odCkge1xuICAgIHZhciBpID0gdC5pbmRleE9mKFwiLlwiKTtcbiAgICBpZiAoaSA+PSAwKSB0ID0gdC5zbGljZSgwLCBpKTtcbiAgICByZXR1cm4gIXQgfHwgdCA9PT0gXCJzdGFydFwiO1xuICB9KTtcbn1cblxuZnVuY3Rpb24gb25GdW5jdGlvbihpZCwgbmFtZSwgbGlzdGVuZXIpIHtcbiAgdmFyIG9uMCwgb24xLCBzaXQgPSBzdGFydChuYW1lKSA/IGluaXQgOiBzZXQ7XG4gIHJldHVybiBmdW5jdGlvbigpIHtcbiAgICB2YXIgc2NoZWR1bGUgPSBzaXQodGhpcywgaWQpLFxuICAgICAgICBvbiA9IHNjaGVkdWxlLm9uO1xuXG4gICAgLy8gSWYgdGhpcyBub2RlIHNoYXJlZCBhIGRpc3BhdGNoIHdpdGggdGhlIHByZXZpb3VzIG5vZGUsXG4gICAgLy8ganVzdCBhc3NpZ24gdGhlIHVwZGF0ZWQgc2hhcmVkIGRpc3BhdGNoIGFuZCB3ZeKAmXJlIGRvbmUhXG4gICAgLy8gT3RoZXJ3aXNlLCBjb3B5LW9uLXdyaXRlLlxuICAgIGlmIChvbiAhPT0gb24wKSAob24xID0gKG9uMCA9IG9uKS5jb3B5KCkpLm9uKG5hbWUsIGxpc3RlbmVyKTtcblxuICAgIHNjaGVkdWxlLm9uID0gb24xO1xuICB9O1xufVxuXG5leHBvcnQgZGVmYXVsdCBmdW5jdGlvbihuYW1lLCBsaXN0ZW5lcikge1xuICB2YXIgaWQgPSB0aGlzLl9pZDtcblxuICByZXR1cm4gYXJndW1lbnRzLmxlbmd0aCA8IDJcbiAgICAgID8gZ2V0KHRoaXMubm9kZSgpLCBpZCkub24ub24obmFtZSlcbiAgICAgIDogdGhpcy5lYWNoKG9uRnVuY3Rpb24oaWQsIG5hbWUsIGxpc3RlbmVyKSk7XG59XG4iLCJmdW5jdGlvbiByZW1vdmVGdW5jdGlvbihpZCkge1xuICByZXR1cm4gZnVuY3Rpb24oKSB7XG4gICAgdmFyIHBhcmVudCA9IHRoaXMucGFyZW50Tm9kZTtcbiAgICBmb3IgKHZhciBpIGluIHRoaXMuX190cmFuc2l0aW9uKSBpZiAoK2kgIT09IGlkKSByZXR1cm47XG4gICAgaWYgKHBhcmVudCkgcGFyZW50LnJlbW92ZUNoaWxkKHRoaXMpO1xuICB9O1xufVxuXG5leHBvcnQgZGVmYXVsdCBmdW5jdGlvbigpIHtcbiAgcmV0dXJuIHRoaXMub24oXCJlbmQucmVtb3ZlXCIsIHJlbW92ZUZ1bmN0aW9uKHRoaXMuX2lkKSk7XG59XG4iLCJpbXBvcnQge3NlbGVjdG9yfSBmcm9tIFwiZDMtc2VsZWN0aW9uXCI7XG5pbXBvcnQge1RyYW5zaXRpb259IGZyb20gXCIuL2luZGV4LmpzXCI7XG5pbXBvcnQgc2NoZWR1bGUsIHtnZXR9IGZyb20gXCIuL3NjaGVkdWxlLmpzXCI7XG5cbmV4cG9ydCBkZWZhdWx0IGZ1bmN0aW9uKHNlbGVjdCkge1xuICB2YXIgbmFtZSA9IHRoaXMuX25hbWUsXG4gICAgICBpZCA9IHRoaXMuX2lkO1xuXG4gIGlmICh0eXBlb2Ygc2VsZWN0ICE9PSBcImZ1bmN0aW9uXCIpIHNlbGVjdCA9IHNlbGVjdG9yKHNlbGVjdCk7XG5cbiAgZm9yICh2YXIgZ3JvdXBzID0gdGhpcy5fZ3JvdXBzLCBtID0gZ3JvdXBzLmxlbmd0aCwgc3ViZ3JvdXBzID0gbmV3IEFycmF5KG0pLCBqID0gMDsgaiA8IG07ICsraikge1xuICAgIGZvciAodmFyIGdyb3VwID0gZ3JvdXBzW2pdLCBuID0gZ3JvdXAubGVuZ3RoLCBzdWJncm91cCA9IHN1Ymdyb3Vwc1tqXSA9IG5ldyBBcnJheShuKSwgbm9kZSwgc3Vibm9kZSwgaSA9IDA7IGkgPCBuOyArK2kpIHtcbiAgICAgIGlmICgobm9kZSA9IGdyb3VwW2ldKSAmJiAoc3Vibm9kZSA9IHNlbGVjdC5jYWxsKG5vZGUsIG5vZGUuX19kYXRhX18sIGksIGdyb3VwKSkpIHtcbiAgICAgICAgaWYgKFwiX19kYXRhX19cIiBpbiBub2RlKSBzdWJub2RlLl9fZGF0YV9fID0gbm9kZS5fX2RhdGFfXztcbiAgICAgICAgc3ViZ3JvdXBbaV0gPSBzdWJub2RlO1xuICAgICAgICBzY2hlZHVsZShzdWJncm91cFtpXSwgbmFtZSwgaWQsIGksIHN1Ymdyb3VwLCBnZXQobm9kZSwgaWQpKTtcbiAgICAgIH1cbiAgICB9XG4gIH1cblxuICByZXR1cm4gbmV3IFRyYW5zaXRpb24oc3ViZ3JvdXBzLCB0aGlzLl9wYXJlbnRzLCBuYW1lLCBpZCk7XG59XG4iLCJpbXBvcnQge3NlbGVjdG9yQWxsfSBmcm9tIFwiZDMtc2VsZWN0aW9uXCI7XG5pbXBvcnQge1RyYW5zaXRpb259IGZyb20gXCIuL2luZGV4LmpzXCI7XG5pbXBvcnQgc2NoZWR1bGUsIHtnZXR9IGZyb20gXCIuL3NjaGVkdWxlLmpzXCI7XG5cbmV4cG9ydCBkZWZhdWx0IGZ1bmN0aW9uKHNlbGVjdCkge1xuICB2YXIgbmFtZSA9IHRoaXMuX25hbWUsXG4gICAgICBpZCA9IHRoaXMuX2lkO1xuXG4gIGlmICh0eXBlb2Ygc2VsZWN0ICE9PSBcImZ1bmN0aW9uXCIpIHNlbGVjdCA9IHNlbGVjdG9yQWxsKHNlbGVjdCk7XG5cbiAgZm9yICh2YXIgZ3JvdXBzID0gdGhpcy5fZ3JvdXBzLCBtID0gZ3JvdXBzLmxlbmd0aCwgc3ViZ3JvdXBzID0gW10sIHBhcmVudHMgPSBbXSwgaiA9IDA7IGogPCBtOyArK2opIHtcbiAgICBmb3IgKHZhciBncm91cCA9IGdyb3Vwc1tqXSwgbiA9IGdyb3VwLmxlbmd0aCwgbm9kZSwgaSA9IDA7IGkgPCBuOyArK2kpIHtcbiAgICAgIGlmIChub2RlID0gZ3JvdXBbaV0pIHtcbiAgICAgICAgZm9yICh2YXIgY2hpbGRyZW4gPSBzZWxlY3QuY2FsbChub2RlLCBub2RlLl9fZGF0YV9fLCBpLCBncm91cCksIGNoaWxkLCBpbmhlcml0ID0gZ2V0KG5vZGUsIGlkKSwgayA9IDAsIGwgPSBjaGlsZHJlbi5sZW5ndGg7IGsgPCBsOyArK2spIHtcbiAgICAgICAgICBpZiAoY2hpbGQgPSBjaGlsZHJlbltrXSkge1xuICAgICAgICAgICAgc2NoZWR1bGUoY2hpbGQsIG5hbWUsIGlkLCBrLCBjaGlsZHJlbiwgaW5oZXJpdCk7XG4gICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICAgIHN1Ymdyb3Vwcy5wdXNoKGNoaWxkcmVuKTtcbiAgICAgICAgcGFyZW50cy5wdXNoKG5vZGUpO1xuICAgICAgfVxuICAgIH1cbiAgfVxuXG4gIHJldHVybiBuZXcgVHJhbnNpdGlvbihzdWJncm91cHMsIHBhcmVudHMsIG5hbWUsIGlkKTtcbn1cbiIsImltcG9ydCB7c2VsZWN0aW9ufSBmcm9tIFwiZDMtc2VsZWN0aW9uXCI7XG5cbnZhciBTZWxlY3Rpb24gPSBzZWxlY3Rpb24ucHJvdG90eXBlLmNvbnN0cnVjdG9yO1xuXG5leHBvcnQgZGVmYXVsdCBmdW5jdGlvbigpIHtcbiAgcmV0dXJuIG5ldyBTZWxlY3Rpb24odGhpcy5fZ3JvdXBzLCB0aGlzLl9wYXJlbnRzKTtcbn1cbiIsImltcG9ydCB7aW50ZXJwb2xhdGVUcmFuc2Zvcm1Dc3MgYXMgaW50ZXJwb2xhdGVUcmFuc2Zvcm19IGZyb20gXCJkMy1pbnRlcnBvbGF0ZVwiO1xuaW1wb3J0IHtzdHlsZX0gZnJvbSBcImQzLXNlbGVjdGlvblwiO1xuaW1wb3J0IHtzZXR9IGZyb20gXCIuL3NjaGVkdWxlLmpzXCI7XG5pbXBvcnQge3R3ZWVuVmFsdWV9IGZyb20gXCIuL3R3ZWVuLmpzXCI7XG5pbXBvcnQgaW50ZXJwb2xhdGUgZnJvbSBcIi4vaW50ZXJwb2xhdGUuanNcIjtcblxuZnVuY3Rpb24gc3R5bGVOdWxsKG5hbWUsIGludGVycG9sYXRlKSB7XG4gIHZhciBzdHJpbmcwMCxcbiAgICAgIHN0cmluZzEwLFxuICAgICAgaW50ZXJwb2xhdGUwO1xuICByZXR1cm4gZnVuY3Rpb24oKSB7XG4gICAgdmFyIHN0cmluZzAgPSBzdHlsZSh0aGlzLCBuYW1lKSxcbiAgICAgICAgc3RyaW5nMSA9ICh0aGlzLnN0eWxlLnJlbW92ZVByb3BlcnR5KG5hbWUpLCBzdHlsZSh0aGlzLCBuYW1lKSk7XG4gICAgcmV0dXJuIHN0cmluZzAgPT09IHN0cmluZzEgPyBudWxsXG4gICAgICAgIDogc3RyaW5nMCA9PT0gc3RyaW5nMDAgJiYgc3RyaW5nMSA9PT0gc3RyaW5nMTAgPyBpbnRlcnBvbGF0ZTBcbiAgICAgICAgOiBpbnRlcnBvbGF0ZTAgPSBpbnRlcnBvbGF0ZShzdHJpbmcwMCA9IHN0cmluZzAsIHN0cmluZzEwID0gc3RyaW5nMSk7XG4gIH07XG59XG5cbmZ1bmN0aW9uIHN0eWxlUmVtb3ZlKG5hbWUpIHtcbiAgcmV0dXJuIGZ1bmN0aW9uKCkge1xuICAgIHRoaXMuc3R5bGUucmVtb3ZlUHJvcGVydHkobmFtZSk7XG4gIH07XG59XG5cbmZ1bmN0aW9uIHN0eWxlQ29uc3RhbnQobmFtZSwgaW50ZXJwb2xhdGUsIHZhbHVlMSkge1xuICB2YXIgc3RyaW5nMDAsXG4gICAgICBzdHJpbmcxID0gdmFsdWUxICsgXCJcIixcbiAgICAgIGludGVycG9sYXRlMDtcbiAgcmV0dXJuIGZ1bmN0aW9uKCkge1xuICAgIHZhciBzdHJpbmcwID0gc3R5bGUodGhpcywgbmFtZSk7XG4gICAgcmV0dXJuIHN0cmluZzAgPT09IHN0cmluZzEgPyBudWxsXG4gICAgICAgIDogc3RyaW5nMCA9PT0gc3RyaW5nMDAgPyBpbnRlcnBvbGF0ZTBcbiAgICAgICAgOiBpbnRlcnBvbGF0ZTAgPSBpbnRlcnBvbGF0ZShzdHJpbmcwMCA9IHN0cmluZzAsIHZhbHVlMSk7XG4gIH07XG59XG5cbmZ1bmN0aW9uIHN0eWxlRnVuY3Rpb24obmFtZSwgaW50ZXJwb2xhdGUsIHZhbHVlKSB7XG4gIHZhciBzdHJpbmcwMCxcbiAgICAgIHN0cmluZzEwLFxuICAgICAgaW50ZXJwb2xhdGUwO1xuICByZXR1cm4gZnVuY3Rpb24oKSB7XG4gICAgdmFyIHN0cmluZzAgPSBzdHlsZSh0aGlzLCBuYW1lKSxcbiAgICAgICAgdmFsdWUxID0gdmFsdWUodGhpcyksXG4gICAgICAgIHN0cmluZzEgPSB2YWx1ZTEgKyBcIlwiO1xuICAgIGlmICh2YWx1ZTEgPT0gbnVsbCkgc3RyaW5nMSA9IHZhbHVlMSA9ICh0aGlzLnN0eWxlLnJlbW92ZVByb3BlcnR5KG5hbWUpLCBzdHlsZSh0aGlzLCBuYW1lKSk7XG4gICAgcmV0dXJuIHN0cmluZzAgPT09IHN0cmluZzEgPyBudWxsXG4gICAgICAgIDogc3RyaW5nMCA9PT0gc3RyaW5nMDAgJiYgc3RyaW5nMSA9PT0gc3RyaW5nMTAgPyBpbnRlcnBvbGF0ZTBcbiAgICAgICAgOiAoc3RyaW5nMTAgPSBzdHJpbmcxLCBpbnRlcnBvbGF0ZTAgPSBpbnRlcnBvbGF0ZShzdHJpbmcwMCA9IHN0cmluZzAsIHZhbHVlMSkpO1xuICB9O1xufVxuXG5mdW5jdGlvbiBzdHlsZU1heWJlUmVtb3ZlKGlkLCBuYW1lKSB7XG4gIHZhciBvbjAsIG9uMSwgbGlzdGVuZXIwLCBrZXkgPSBcInN0eWxlLlwiICsgbmFtZSwgZXZlbnQgPSBcImVuZC5cIiArIGtleSwgcmVtb3ZlO1xuICByZXR1cm4gZnVuY3Rpb24oKSB7XG4gICAgdmFyIHNjaGVkdWxlID0gc2V0KHRoaXMsIGlkKSxcbiAgICAgICAgb24gPSBzY2hlZHVsZS5vbixcbiAgICAgICAgbGlzdGVuZXIgPSBzY2hlZHVsZS52YWx1ZVtrZXldID09IG51bGwgPyByZW1vdmUgfHwgKHJlbW92ZSA9IHN0eWxlUmVtb3ZlKG5hbWUpKSA6IHVuZGVmaW5lZDtcblxuICAgIC8vIElmIHRoaXMgbm9kZSBzaGFyZWQgYSBkaXNwYXRjaCB3aXRoIHRoZSBwcmV2aW91cyBub2RlLFxuICAgIC8vIGp1c3QgYXNzaWduIHRoZSB1cGRhdGVkIHNoYXJlZCBkaXNwYXRjaCBhbmQgd2XigJlyZSBkb25lIVxuICAgIC8vIE90aGVyd2lzZSwgY29weS1vbi13cml0ZS5cbiAgICBpZiAob24gIT09IG9uMCB8fCBsaXN0ZW5lcjAgIT09IGxpc3RlbmVyKSAob24xID0gKG9uMCA9IG9uKS5jb3B5KCkpLm9uKGV2ZW50LCBsaXN0ZW5lcjAgPSBsaXN0ZW5lcik7XG5cbiAgICBzY2hlZHVsZS5vbiA9IG9uMTtcbiAgfTtcbn1cblxuZXhwb3J0IGRlZmF1bHQgZnVuY3Rpb24obmFtZSwgdmFsdWUsIHByaW9yaXR5KSB7XG4gIHZhciBpID0gKG5hbWUgKz0gXCJcIikgPT09IFwidHJhbnNmb3JtXCIgPyBpbnRlcnBvbGF0ZVRyYW5zZm9ybSA6IGludGVycG9sYXRlO1xuICByZXR1cm4gdmFsdWUgPT0gbnVsbCA/IHRoaXNcbiAgICAgIC5zdHlsZVR3ZWVuKG5hbWUsIHN0eWxlTnVsbChuYW1lLCBpKSlcbiAgICAgIC5vbihcImVuZC5zdHlsZS5cIiArIG5hbWUsIHN0eWxlUmVtb3ZlKG5hbWUpKVxuICAgIDogdHlwZW9mIHZhbHVlID09PSBcImZ1bmN0aW9uXCIgPyB0aGlzXG4gICAgICAuc3R5bGVUd2VlbihuYW1lLCBzdHlsZUZ1bmN0aW9uKG5hbWUsIGksIHR3ZWVuVmFsdWUodGhpcywgXCJzdHlsZS5cIiArIG5hbWUsIHZhbHVlKSkpXG4gICAgICAuZWFjaChzdHlsZU1heWJlUmVtb3ZlKHRoaXMuX2lkLCBuYW1lKSlcbiAgICA6IHRoaXNcbiAgICAgIC5zdHlsZVR3ZWVuKG5hbWUsIHN0eWxlQ29uc3RhbnQobmFtZSwgaSwgdmFsdWUpLCBwcmlvcml0eSlcbiAgICAgIC5vbihcImVuZC5zdHlsZS5cIiArIG5hbWUsIG51bGwpO1xufVxuIiwiZnVuY3Rpb24gc3R5bGVJbnRlcnBvbGF0ZShuYW1lLCBpLCBwcmlvcml0eSkge1xuICByZXR1cm4gZnVuY3Rpb24odCkge1xuICAgIHRoaXMuc3R5bGUuc2V0UHJvcGVydHkobmFtZSwgaS5jYWxsKHRoaXMsIHQpLCBwcmlvcml0eSk7XG4gIH07XG59XG5cbmZ1bmN0aW9uIHN0eWxlVHdlZW4obmFtZSwgdmFsdWUsIHByaW9yaXR5KSB7XG4gIHZhciB0LCBpMDtcbiAgZnVuY3Rpb24gdHdlZW4oKSB7XG4gICAgdmFyIGkgPSB2YWx1ZS5hcHBseSh0aGlzLCBhcmd1bWVudHMpO1xuICAgIGlmIChpICE9PSBpMCkgdCA9IChpMCA9IGkpICYmIHN0eWxlSW50ZXJwb2xhdGUobmFtZSwgaSwgcHJpb3JpdHkpO1xuICAgIHJldHVybiB0O1xuICB9XG4gIHR3ZWVuLl92YWx1ZSA9IHZhbHVlO1xuICByZXR1cm4gdHdlZW47XG59XG5cbmV4cG9ydCBkZWZhdWx0IGZ1bmN0aW9uKG5hbWUsIHZhbHVlLCBwcmlvcml0eSkge1xuICB2YXIga2V5ID0gXCJzdHlsZS5cIiArIChuYW1lICs9IFwiXCIpO1xuICBpZiAoYXJndW1lbnRzLmxlbmd0aCA8IDIpIHJldHVybiAoa2V5ID0gdGhpcy50d2VlbihrZXkpKSAmJiBrZXkuX3ZhbHVlO1xuICBpZiAodmFsdWUgPT0gbnVsbCkgcmV0dXJuIHRoaXMudHdlZW4oa2V5LCBudWxsKTtcbiAgaWYgKHR5cGVvZiB2YWx1ZSAhPT0gXCJmdW5jdGlvblwiKSB0aHJvdyBuZXcgRXJyb3I7XG4gIHJldHVybiB0aGlzLnR3ZWVuKGtleSwgc3R5bGVUd2VlbihuYW1lLCB2YWx1ZSwgcHJpb3JpdHkgPT0gbnVsbCA/IFwiXCIgOiBwcmlvcml0eSkpO1xufVxuIiwiaW1wb3J0IHt0d2VlblZhbHVlfSBmcm9tIFwiLi90d2Vlbi5qc1wiO1xuXG5mdW5jdGlvbiB0ZXh0Q29uc3RhbnQodmFsdWUpIHtcbiAgcmV0dXJuIGZ1bmN0aW9uKCkge1xuICAgIHRoaXMudGV4dENvbnRlbnQgPSB2YWx1ZTtcbiAgfTtcbn1cblxuZnVuY3Rpb24gdGV4dEZ1bmN0aW9uKHZhbHVlKSB7XG4gIHJldHVybiBmdW5jdGlvbigpIHtcbiAgICB2YXIgdmFsdWUxID0gdmFsdWUodGhpcyk7XG4gICAgdGhpcy50ZXh0Q29udGVudCA9IHZhbHVlMSA9PSBudWxsID8gXCJcIiA6IHZhbHVlMTtcbiAgfTtcbn1cblxuZXhwb3J0IGRlZmF1bHQgZnVuY3Rpb24odmFsdWUpIHtcbiAgcmV0dXJuIHRoaXMudHdlZW4oXCJ0ZXh0XCIsIHR5cGVvZiB2YWx1ZSA9PT0gXCJmdW5jdGlvblwiXG4gICAgICA/IHRleHRGdW5jdGlvbih0d2VlblZhbHVlKHRoaXMsIFwidGV4dFwiLCB2YWx1ZSkpXG4gICAgICA6IHRleHRDb25zdGFudCh2YWx1ZSA9PSBudWxsID8gXCJcIiA6IHZhbHVlICsgXCJcIikpO1xufVxuIiwiZnVuY3Rpb24gdGV4dEludGVycG9sYXRlKGkpIHtcbiAgcmV0dXJuIGZ1bmN0aW9uKHQpIHtcbiAgICB0aGlzLnRleHRDb250ZW50ID0gaS5jYWxsKHRoaXMsIHQpO1xuICB9O1xufVxuXG5mdW5jdGlvbiB0ZXh0VHdlZW4odmFsdWUpIHtcbiAgdmFyIHQwLCBpMDtcbiAgZnVuY3Rpb24gdHdlZW4oKSB7XG4gICAgdmFyIGkgPSB2YWx1ZS5hcHBseSh0aGlzLCBhcmd1bWVudHMpO1xuICAgIGlmIChpICE9PSBpMCkgdDAgPSAoaTAgPSBpKSAmJiB0ZXh0SW50ZXJwb2xhdGUoaSk7XG4gICAgcmV0dXJuIHQwO1xuICB9XG4gIHR3ZWVuLl92YWx1ZSA9IHZhbHVlO1xuICByZXR1cm4gdHdlZW47XG59XG5cbmV4cG9ydCBkZWZhdWx0IGZ1bmN0aW9uKHZhbHVlKSB7XG4gIHZhciBrZXkgPSBcInRleHRcIjtcbiAgaWYgKGFyZ3VtZW50cy5sZW5ndGggPCAxKSByZXR1cm4gKGtleSA9IHRoaXMudHdlZW4oa2V5KSkgJiYga2V5Ll92YWx1ZTtcbiAgaWYgKHZhbHVlID09IG51bGwpIHJldHVybiB0aGlzLnR3ZWVuKGtleSwgbnVsbCk7XG4gIGlmICh0eXBlb2YgdmFsdWUgIT09IFwiZnVuY3Rpb25cIikgdGhyb3cgbmV3IEVycm9yO1xuICByZXR1cm4gdGhpcy50d2VlbihrZXksIHRleHRUd2Vlbih2YWx1ZSkpO1xufVxuIiwiaW1wb3J0IHtUcmFuc2l0aW9uLCBuZXdJZH0gZnJvbSBcIi4vaW5kZXguanNcIjtcbmltcG9ydCBzY2hlZHVsZSwge2dldH0gZnJvbSBcIi4vc2NoZWR1bGUuanNcIjtcblxuZXhwb3J0IGRlZmF1bHQgZnVuY3Rpb24oKSB7XG4gIHZhciBuYW1lID0gdGhpcy5fbmFtZSxcbiAgICAgIGlkMCA9IHRoaXMuX2lkLFxuICAgICAgaWQxID0gbmV3SWQoKTtcblxuICBmb3IgKHZhciBncm91cHMgPSB0aGlzLl9ncm91cHMsIG0gPSBncm91cHMubGVuZ3RoLCBqID0gMDsgaiA8IG07ICsraikge1xuICAgIGZvciAodmFyIGdyb3VwID0gZ3JvdXBzW2pdLCBuID0gZ3JvdXAubGVuZ3RoLCBub2RlLCBpID0gMDsgaSA8IG47ICsraSkge1xuICAgICAgaWYgKG5vZGUgPSBncm91cFtpXSkge1xuICAgICAgICB2YXIgaW5oZXJpdCA9IGdldChub2RlLCBpZDApO1xuICAgICAgICBzY2hlZHVsZShub2RlLCBuYW1lLCBpZDEsIGksIGdyb3VwLCB7XG4gICAgICAgICAgdGltZTogaW5oZXJpdC50aW1lICsgaW5oZXJpdC5kZWxheSArIGluaGVyaXQuZHVyYXRpb24sXG4gICAgICAgICAgZGVsYXk6IDAsXG4gICAgICAgICAgZHVyYXRpb246IGluaGVyaXQuZHVyYXRpb24sXG4gICAgICAgICAgZWFzZTogaW5oZXJpdC5lYXNlXG4gICAgICAgIH0pO1xuICAgICAgfVxuICAgIH1cbiAgfVxuXG4gIHJldHVybiBuZXcgVHJhbnNpdGlvbihncm91cHMsIHRoaXMuX3BhcmVudHMsIG5hbWUsIGlkMSk7XG59XG4iLCJpbXBvcnQge3NldH0gZnJvbSBcIi4vc2NoZWR1bGUuanNcIjtcblxuZXhwb3J0IGRlZmF1bHQgZnVuY3Rpb24oKSB7XG4gIHZhciBvbjAsIG9uMSwgdGhhdCA9IHRoaXMsIGlkID0gdGhhdC5faWQsIHNpemUgPSB0aGF0LnNpemUoKTtcbiAgcmV0dXJuIG5ldyBQcm9taXNlKGZ1bmN0aW9uKHJlc29sdmUsIHJlamVjdCkge1xuICAgIHZhciBjYW5jZWwgPSB7dmFsdWU6IHJlamVjdH0sXG4gICAgICAgIGVuZCA9IHt2YWx1ZTogZnVuY3Rpb24oKSB7IGlmICgtLXNpemUgPT09IDApIHJlc29sdmUoKTsgfX07XG5cbiAgICB0aGF0LmVhY2goZnVuY3Rpb24oKSB7XG4gICAgICB2YXIgc2NoZWR1bGUgPSBzZXQodGhpcywgaWQpLFxuICAgICAgICAgIG9uID0gc2NoZWR1bGUub247XG5cbiAgICAgIC8vIElmIHRoaXMgbm9kZSBzaGFyZWQgYSBkaXNwYXRjaCB3aXRoIHRoZSBwcmV2aW91cyBub2RlLFxuICAgICAgLy8ganVzdCBhc3NpZ24gdGhlIHVwZGF0ZWQgc2hhcmVkIGRpc3BhdGNoIGFuZCB3ZeKAmXJlIGRvbmUhXG4gICAgICAvLyBPdGhlcndpc2UsIGNvcHktb24td3JpdGUuXG4gICAgICBpZiAob24gIT09IG9uMCkge1xuICAgICAgICBvbjEgPSAob24wID0gb24pLmNvcHkoKTtcbiAgICAgICAgb24xLl8uY2FuY2VsLnB1c2goY2FuY2VsKTtcbiAgICAgICAgb24xLl8uaW50ZXJydXB0LnB1c2goY2FuY2VsKTtcbiAgICAgICAgb24xLl8uZW5kLnB1c2goZW5kKTtcbiAgICAgIH1cblxuICAgICAgc2NoZWR1bGUub24gPSBvbjE7XG4gICAgfSk7XG5cbiAgICAvLyBUaGUgc2VsZWN0aW9uIHdhcyBlbXB0eSwgcmVzb2x2ZSBlbmQgaW1tZWRpYXRlbHlcbiAgICBpZiAoc2l6ZSA9PT0gMCkgcmVzb2x2ZSgpO1xuICB9KTtcbn1cbiIsImltcG9ydCB7c2VsZWN0aW9ufSBmcm9tIFwiZDMtc2VsZWN0aW9uXCI7XG5pbXBvcnQgdHJhbnNpdGlvbl9hdHRyIGZyb20gXCIuL2F0dHIuanNcIjtcbmltcG9ydCB0cmFuc2l0aW9uX2F0dHJUd2VlbiBmcm9tIFwiLi9hdHRyVHdlZW4uanNcIjtcbmltcG9ydCB0cmFuc2l0aW9uX2RlbGF5IGZyb20gXCIuL2RlbGF5LmpzXCI7XG5pbXBvcnQgdHJhbnNpdGlvbl9kdXJhdGlvbiBmcm9tIFwiLi9kdXJhdGlvbi5qc1wiO1xuaW1wb3J0IHRyYW5zaXRpb25fZWFzZSBmcm9tIFwiLi9lYXNlLmpzXCI7XG5pbXBvcnQgdHJhbnNpdGlvbl9lYXNlVmFyeWluZyBmcm9tIFwiLi9lYXNlVmFyeWluZy5qc1wiO1xuaW1wb3J0IHRyYW5zaXRpb25fZmlsdGVyIGZyb20gXCIuL2ZpbHRlci5qc1wiO1xuaW1wb3J0IHRyYW5zaXRpb25fbWVyZ2UgZnJvbSBcIi4vbWVyZ2UuanNcIjtcbmltcG9ydCB0cmFuc2l0aW9uX29uIGZyb20gXCIuL29uLmpzXCI7XG5pbXBvcnQgdHJhbnNpdGlvbl9yZW1vdmUgZnJvbSBcIi4vcmVtb3ZlLmpzXCI7XG5pbXBvcnQgdHJhbnNpdGlvbl9zZWxlY3QgZnJvbSBcIi4vc2VsZWN0LmpzXCI7XG5pbXBvcnQgdHJhbnNpdGlvbl9zZWxlY3RBbGwgZnJvbSBcIi4vc2VsZWN0QWxsLmpzXCI7XG5pbXBvcnQgdHJhbnNpdGlvbl9zZWxlY3Rpb24gZnJvbSBcIi4vc2VsZWN0aW9uLmpzXCI7XG5pbXBvcnQgdHJhbnNpdGlvbl9zdHlsZSBmcm9tIFwiLi9zdHlsZS5qc1wiO1xuaW1wb3J0IHRyYW5zaXRpb25fc3R5bGVUd2VlbiBmcm9tIFwiLi9zdHlsZVR3ZWVuLmpzXCI7XG5pbXBvcnQgdHJhbnNpdGlvbl90ZXh0IGZyb20gXCIuL3RleHQuanNcIjtcbmltcG9ydCB0cmFuc2l0aW9uX3RleHRUd2VlbiBmcm9tIFwiLi90ZXh0VHdlZW4uanNcIjtcbmltcG9ydCB0cmFuc2l0aW9uX3RyYW5zaXRpb24gZnJvbSBcIi4vdHJhbnNpdGlvbi5qc1wiO1xuaW1wb3J0IHRyYW5zaXRpb25fdHdlZW4gZnJvbSBcIi4vdHdlZW4uanNcIjtcbmltcG9ydCB0cmFuc2l0aW9uX2VuZCBmcm9tIFwiLi9lbmQuanNcIjtcblxudmFyIGlkID0gMDtcblxuZXhwb3J0IGZ1bmN0aW9uIFRyYW5zaXRpb24oZ3JvdXBzLCBwYXJlbnRzLCBuYW1lLCBpZCkge1xuICB0aGlzLl9ncm91cHMgPSBncm91cHM7XG4gIHRoaXMuX3BhcmVudHMgPSBwYXJlbnRzO1xuICB0aGlzLl9uYW1lID0gbmFtZTtcbiAgdGhpcy5faWQgPSBpZDtcbn1cblxuZXhwb3J0IGRlZmF1bHQgZnVuY3Rpb24gdHJhbnNpdGlvbihuYW1lKSB7XG4gIHJldHVybiBzZWxlY3Rpb24oKS50cmFuc2l0aW9uKG5hbWUpO1xufVxuXG5leHBvcnQgZnVuY3Rpb24gbmV3SWQoKSB7XG4gIHJldHVybiArK2lkO1xufVxuXG52YXIgc2VsZWN0aW9uX3Byb3RvdHlwZSA9IHNlbGVjdGlvbi5wcm90b3R5cGU7XG5cblRyYW5zaXRpb24ucHJvdG90eXBlID0gdHJhbnNpdGlvbi5wcm90b3R5cGUgPSB7XG4gIGNvbnN0cnVjdG9yOiBUcmFuc2l0aW9uLFxuICBzZWxlY3Q6IHRyYW5zaXRpb25fc2VsZWN0LFxuICBzZWxlY3RBbGw6IHRyYW5zaXRpb25fc2VsZWN0QWxsLFxuICBzZWxlY3RDaGlsZDogc2VsZWN0aW9uX3Byb3RvdHlwZS5zZWxlY3RDaGlsZCxcbiAgc2VsZWN0Q2hpbGRyZW46IHNlbGVjdGlvbl9wcm90b3R5cGUuc2VsZWN0Q2hpbGRyZW4sXG4gIGZpbHRlcjogdHJhbnNpdGlvbl9maWx0ZXIsXG4gIG1lcmdlOiB0cmFuc2l0aW9uX21lcmdlLFxuICBzZWxlY3Rpb246IHRyYW5zaXRpb25fc2VsZWN0aW9uLFxuICB0cmFuc2l0aW9uOiB0cmFuc2l0aW9uX3RyYW5zaXRpb24sXG4gIGNhbGw6IHNlbGVjdGlvbl9wcm90b3R5cGUuY2FsbCxcbiAgbm9kZXM6IHNlbGVjdGlvbl9wcm90b3R5cGUubm9kZXMsXG4gIG5vZGU6IHNlbGVjdGlvbl9wcm90b3R5cGUubm9kZSxcbiAgc2l6ZTogc2VsZWN0aW9uX3Byb3RvdHlwZS5zaXplLFxuICBlbXB0eTogc2VsZWN0aW9uX3Byb3RvdHlwZS5lbXB0eSxcbiAgZWFjaDogc2VsZWN0aW9uX3Byb3RvdHlwZS5lYWNoLFxuICBvbjogdHJhbnNpdGlvbl9vbixcbiAgYXR0cjogdHJhbnNpdGlvbl9hdHRyLFxuICBhdHRyVHdlZW46IHRyYW5zaXRpb25fYXR0clR3ZWVuLFxuICBzdHlsZTogdHJhbnNpdGlvbl9zdHlsZSxcbiAgc3R5bGVUd2VlbjogdHJhbnNpdGlvbl9zdHlsZVR3ZWVuLFxuICB0ZXh0OiB0cmFuc2l0aW9uX3RleHQsXG4gIHRleHRUd2VlbjogdHJhbnNpdGlvbl90ZXh0VHdlZW4sXG4gIHJlbW92ZTogdHJhbnNpdGlvbl9yZW1vdmUsXG4gIHR3ZWVuOiB0cmFuc2l0aW9uX3R3ZWVuLFxuICBkZWxheTogdHJhbnNpdGlvbl9kZWxheSxcbiAgZHVyYXRpb246IHRyYW5zaXRpb25fZHVyYXRpb24sXG4gIGVhc2U6IHRyYW5zaXRpb25fZWFzZSxcbiAgZWFzZVZhcnlpbmc6IHRyYW5zaXRpb25fZWFzZVZhcnlpbmcsXG4gIGVuZDogdHJhbnNpdGlvbl9lbmQsXG4gIFtTeW1ib2wuaXRlcmF0b3JdOiBzZWxlY3Rpb25fcHJvdG90eXBlW1N5bWJvbC5pdGVyYXRvcl1cbn07XG4iLCJleHBvcnQgZnVuY3Rpb24gY3ViaWNJbih0KSB7XG4gIHJldHVybiB0ICogdCAqIHQ7XG59XG5cbmV4cG9ydCBmdW5jdGlvbiBjdWJpY091dCh0KSB7XG4gIHJldHVybiAtLXQgKiB0ICogdCArIDE7XG59XG5cbmV4cG9ydCBmdW5jdGlvbiBjdWJpY0luT3V0KHQpIHtcbiAgcmV0dXJuICgodCAqPSAyKSA8PSAxID8gdCAqIHQgKiB0IDogKHQgLT0gMikgKiB0ICogdCArIDIpIC8gMjtcbn1cbiIsImltcG9ydCB7VHJhbnNpdGlvbiwgbmV3SWR9IGZyb20gXCIuLi90cmFuc2l0aW9uL2luZGV4LmpzXCI7XG5pbXBvcnQgc2NoZWR1bGUgZnJvbSBcIi4uL3RyYW5zaXRpb24vc2NoZWR1bGUuanNcIjtcbmltcG9ydCB7ZWFzZUN1YmljSW5PdXR9IGZyb20gXCJkMy1lYXNlXCI7XG5pbXBvcnQge25vd30gZnJvbSBcImQzLXRpbWVyXCI7XG5cbnZhciBkZWZhdWx0VGltaW5nID0ge1xuICB0aW1lOiBudWxsLCAvLyBTZXQgb24gdXNlLlxuICBkZWxheTogMCxcbiAgZHVyYXRpb246IDI1MCxcbiAgZWFzZTogZWFzZUN1YmljSW5PdXRcbn07XG5cbmZ1bmN0aW9uIGluaGVyaXQobm9kZSwgaWQpIHtcbiAgdmFyIHRpbWluZztcbiAgd2hpbGUgKCEodGltaW5nID0gbm9kZS5fX3RyYW5zaXRpb24pIHx8ICEodGltaW5nID0gdGltaW5nW2lkXSkpIHtcbiAgICBpZiAoIShub2RlID0gbm9kZS5wYXJlbnROb2RlKSkge1xuICAgICAgdGhyb3cgbmV3IEVycm9yKGB0cmFuc2l0aW9uICR7aWR9IG5vdCBmb3VuZGApO1xuICAgIH1cbiAgfVxuICByZXR1cm4gdGltaW5nO1xufVxuXG5leHBvcnQgZGVmYXVsdCBmdW5jdGlvbihuYW1lKSB7XG4gIHZhciBpZCxcbiAgICAgIHRpbWluZztcblxuICBpZiAobmFtZSBpbnN0YW5jZW9mIFRyYW5zaXRpb24pIHtcbiAgICBpZCA9IG5hbWUuX2lkLCBuYW1lID0gbmFtZS5fbmFtZTtcbiAgfSBlbHNlIHtcbiAgICBpZCA9IG5ld0lkKCksICh0aW1pbmcgPSBkZWZhdWx0VGltaW5nKS50aW1lID0gbm93KCksIG5hbWUgPSBuYW1lID09IG51bGwgPyBudWxsIDogbmFtZSArIFwiXCI7XG4gIH1cblxuICBmb3IgKHZhciBncm91cHMgPSB0aGlzLl9ncm91cHMsIG0gPSBncm91cHMubGVuZ3RoLCBqID0gMDsgaiA8IG07ICsraikge1xuICAgIGZvciAodmFyIGdyb3VwID0gZ3JvdXBzW2pdLCBuID0gZ3JvdXAubGVuZ3RoLCBub2RlLCBpID0gMDsgaSA8IG47ICsraSkge1xuICAgICAgaWYgKG5vZGUgPSBncm91cFtpXSkge1xuICAgICAgICBzY2hlZHVsZShub2RlLCBuYW1lLCBpZCwgaSwgZ3JvdXAsIHRpbWluZyB8fCBpbmhlcml0KG5vZGUsIGlkKSk7XG4gICAgICB9XG4gICAgfVxuICB9XG5cbiAgcmV0dXJuIG5ldyBUcmFuc2l0aW9uKGdyb3VwcywgdGhpcy5fcGFyZW50cywgbmFtZSwgaWQpO1xufVxuIiwiaW1wb3J0IHtzZWxlY3Rpb259IGZyb20gXCJkMy1zZWxlY3Rpb25cIjtcbmltcG9ydCBzZWxlY3Rpb25faW50ZXJydXB0IGZyb20gXCIuL2ludGVycnVwdC5qc1wiO1xuaW1wb3J0IHNlbGVjdGlvbl90cmFuc2l0aW9uIGZyb20gXCIuL3RyYW5zaXRpb24uanNcIjtcblxuc2VsZWN0aW9uLnByb3RvdHlwZS5pbnRlcnJ1cHQgPSBzZWxlY3Rpb25faW50ZXJydXB0O1xuc2VsZWN0aW9uLnByb3RvdHlwZS50cmFuc2l0aW9uID0gc2VsZWN0aW9uX3RyYW5zaXRpb247XG4iLCJleHBvcnQgZGVmYXVsdCB4ID0+ICgpID0+IHg7XG4iLCJleHBvcnQgZGVmYXVsdCBmdW5jdGlvbiBab29tRXZlbnQodHlwZSwge1xuICBzb3VyY2VFdmVudCxcbiAgdGFyZ2V0LFxuICB0cmFuc2Zvcm0sXG4gIGRpc3BhdGNoXG59KSB7XG4gIE9iamVjdC5kZWZpbmVQcm9wZXJ0aWVzKHRoaXMsIHtcbiAgICB0eXBlOiB7dmFsdWU6IHR5cGUsIGVudW1lcmFibGU6IHRydWUsIGNvbmZpZ3VyYWJsZTogdHJ1ZX0sXG4gICAgc291cmNlRXZlbnQ6IHt2YWx1ZTogc291cmNlRXZlbnQsIGVudW1lcmFibGU6IHRydWUsIGNvbmZpZ3VyYWJsZTogdHJ1ZX0sXG4gICAgdGFyZ2V0OiB7dmFsdWU6IHRhcmdldCwgZW51bWVyYWJsZTogdHJ1ZSwgY29uZmlndXJhYmxlOiB0cnVlfSxcbiAgICB0cmFuc2Zvcm06IHt2YWx1ZTogdHJhbnNmb3JtLCBlbnVtZXJhYmxlOiB0cnVlLCBjb25maWd1cmFibGU6IHRydWV9LFxuICAgIF86IHt2YWx1ZTogZGlzcGF0Y2h9XG4gIH0pO1xufVxuIiwiZXhwb3J0IGZ1bmN0aW9uIFRyYW5zZm9ybShrLCB4LCB5KSB7XG4gIHRoaXMuayA9IGs7XG4gIHRoaXMueCA9IHg7XG4gIHRoaXMueSA9IHk7XG59XG5cblRyYW5zZm9ybS5wcm90b3R5cGUgPSB7XG4gIGNvbnN0cnVjdG9yOiBUcmFuc2Zvcm0sXG4gIHNjYWxlOiBmdW5jdGlvbihrKSB7XG4gICAgcmV0dXJuIGsgPT09IDEgPyB0aGlzIDogbmV3IFRyYW5zZm9ybSh0aGlzLmsgKiBrLCB0aGlzLngsIHRoaXMueSk7XG4gIH0sXG4gIHRyYW5zbGF0ZTogZnVuY3Rpb24oeCwgeSkge1xuICAgIHJldHVybiB4ID09PSAwICYgeSA9PT0gMCA/IHRoaXMgOiBuZXcgVHJhbnNmb3JtKHRoaXMuaywgdGhpcy54ICsgdGhpcy5rICogeCwgdGhpcy55ICsgdGhpcy5rICogeSk7XG4gIH0sXG4gIGFwcGx5OiBmdW5jdGlvbihwb2ludCkge1xuICAgIHJldHVybiBbcG9pbnRbMF0gKiB0aGlzLmsgKyB0aGlzLngsIHBvaW50WzFdICogdGhpcy5rICsgdGhpcy55XTtcbiAgfSxcbiAgYXBwbHlYOiBmdW5jdGlvbih4KSB7XG4gICAgcmV0dXJuIHggKiB0aGlzLmsgKyB0aGlzLng7XG4gIH0sXG4gIGFwcGx5WTogZnVuY3Rpb24oeSkge1xuICAgIHJldHVybiB5ICogdGhpcy5rICsgdGhpcy55O1xuICB9LFxuICBpbnZlcnQ6IGZ1bmN0aW9uKGxvY2F0aW9uKSB7XG4gICAgcmV0dXJuIFsobG9jYXRpb25bMF0gLSB0aGlzLngpIC8gdGhpcy5rLCAobG9jYXRpb25bMV0gLSB0aGlzLnkpIC8gdGhpcy5rXTtcbiAgfSxcbiAgaW52ZXJ0WDogZnVuY3Rpb24oeCkge1xuICAgIHJldHVybiAoeCAtIHRoaXMueCkgLyB0aGlzLms7XG4gIH0sXG4gIGludmVydFk6IGZ1bmN0aW9uKHkpIHtcbiAgICByZXR1cm4gKHkgLSB0aGlzLnkpIC8gdGhpcy5rO1xuICB9LFxuICByZXNjYWxlWDogZnVuY3Rpb24oeCkge1xuICAgIHJldHVybiB4LmNvcHkoKS5kb21haW4oeC5yYW5nZSgpLm1hcCh0aGlzLmludmVydFgsIHRoaXMpLm1hcCh4LmludmVydCwgeCkpO1xuICB9LFxuICByZXNjYWxlWTogZnVuY3Rpb24oeSkge1xuICAgIHJldHVybiB5LmNvcHkoKS5kb21haW4oeS5yYW5nZSgpLm1hcCh0aGlzLmludmVydFksIHRoaXMpLm1hcCh5LmludmVydCwgeSkpO1xuICB9LFxuICB0b1N0cmluZzogZnVuY3Rpb24oKSB7XG4gICAgcmV0dXJuIFwidHJhbnNsYXRlKFwiICsgdGhpcy54ICsgXCIsXCIgKyB0aGlzLnkgKyBcIikgc2NhbGUoXCIgKyB0aGlzLmsgKyBcIilcIjtcbiAgfVxufTtcblxuZXhwb3J0IHZhciBpZGVudGl0eSA9IG5ldyBUcmFuc2Zvcm0oMSwgMCwgMCk7XG5cbnRyYW5zZm9ybS5wcm90b3R5cGUgPSBUcmFuc2Zvcm0ucHJvdG90eXBlO1xuXG5leHBvcnQgZGVmYXVsdCBmdW5jdGlvbiB0cmFuc2Zvcm0obm9kZSkge1xuICB3aGlsZSAoIW5vZGUuX196b29tKSBpZiAoIShub2RlID0gbm9kZS5wYXJlbnROb2RlKSkgcmV0dXJuIGlkZW50aXR5O1xuICByZXR1cm4gbm9kZS5fX3pvb207XG59XG4iLCJleHBvcnQgZnVuY3Rpb24gbm9wcm9wYWdhdGlvbihldmVudCkge1xuICBldmVudC5zdG9wSW1tZWRpYXRlUHJvcGFnYXRpb24oKTtcbn1cblxuZXhwb3J0IGRlZmF1bHQgZnVuY3Rpb24oZXZlbnQpIHtcbiAgZXZlbnQucHJldmVudERlZmF1bHQoKTtcbiAgZXZlbnQuc3RvcEltbWVkaWF0ZVByb3BhZ2F0aW9uKCk7XG59XG4iLCJpbXBvcnQge2Rpc3BhdGNofSBmcm9tIFwiZDMtZGlzcGF0Y2hcIjtcbmltcG9ydCB7ZHJhZ0Rpc2FibGUsIGRyYWdFbmFibGV9IGZyb20gXCJkMy1kcmFnXCI7XG5pbXBvcnQge2ludGVycG9sYXRlWm9vbX0gZnJvbSBcImQzLWludGVycG9sYXRlXCI7XG5pbXBvcnQge3NlbGVjdCwgcG9pbnRlcn0gZnJvbSBcImQzLXNlbGVjdGlvblwiO1xuaW1wb3J0IHtpbnRlcnJ1cHR9IGZyb20gXCJkMy10cmFuc2l0aW9uXCI7XG5pbXBvcnQgY29uc3RhbnQgZnJvbSBcIi4vY29uc3RhbnQuanNcIjtcbmltcG9ydCBab29tRXZlbnQgZnJvbSBcIi4vZXZlbnQuanNcIjtcbmltcG9ydCB7VHJhbnNmb3JtLCBpZGVudGl0eX0gZnJvbSBcIi4vdHJhbnNmb3JtLmpzXCI7XG5pbXBvcnQgbm9ldmVudCwge25vcHJvcGFnYXRpb259IGZyb20gXCIuL25vZXZlbnQuanNcIjtcblxuLy8gSWdub3JlIHJpZ2h0LWNsaWNrLCBzaW5jZSB0aGF0IHNob3VsZCBvcGVuIHRoZSBjb250ZXh0IG1lbnUuXG4vLyBleGNlcHQgZm9yIHBpbmNoLXRvLXpvb20sIHdoaWNoIGlzIHNlbnQgYXMgYSB3aGVlbCtjdHJsS2V5IGV2ZW50XG5mdW5jdGlvbiBkZWZhdWx0RmlsdGVyKGV2ZW50KSB7XG4gIHJldHVybiAoIWV2ZW50LmN0cmxLZXkgfHwgZXZlbnQudHlwZSA9PT0gJ3doZWVsJykgJiYgIWV2ZW50LmJ1dHRvbjtcbn1cblxuZnVuY3Rpb24gZGVmYXVsdEV4dGVudCgpIHtcbiAgdmFyIGUgPSB0aGlzO1xuICBpZiAoZSBpbnN0YW5jZW9mIFNWR0VsZW1lbnQpIHtcbiAgICBlID0gZS5vd25lclNWR0VsZW1lbnQgfHwgZTtcbiAgICBpZiAoZS5oYXNBdHRyaWJ1dGUoXCJ2aWV3Qm94XCIpKSB7XG4gICAgICBlID0gZS52aWV3Qm94LmJhc2VWYWw7XG4gICAgICByZXR1cm4gW1tlLngsIGUueV0sIFtlLnggKyBlLndpZHRoLCBlLnkgKyBlLmhlaWdodF1dO1xuICAgIH1cbiAgICByZXR1cm4gW1swLCAwXSwgW2Uud2lkdGguYmFzZVZhbC52YWx1ZSwgZS5oZWlnaHQuYmFzZVZhbC52YWx1ZV1dO1xuICB9XG4gIHJldHVybiBbWzAsIDBdLCBbZS5jbGllbnRXaWR0aCwgZS5jbGllbnRIZWlnaHRdXTtcbn1cblxuZnVuY3Rpb24gZGVmYXVsdFRyYW5zZm9ybSgpIHtcbiAgcmV0dXJuIHRoaXMuX196b29tIHx8IGlkZW50aXR5O1xufVxuXG5mdW5jdGlvbiBkZWZhdWx0V2hlZWxEZWx0YShldmVudCkge1xuICByZXR1cm4gLWV2ZW50LmRlbHRhWSAqIChldmVudC5kZWx0YU1vZGUgPT09IDEgPyAwLjA1IDogZXZlbnQuZGVsdGFNb2RlID8gMSA6IDAuMDAyKSAqIChldmVudC5jdHJsS2V5ID8gMTAgOiAxKTtcbn1cblxuZnVuY3Rpb24gZGVmYXVsdFRvdWNoYWJsZSgpIHtcbiAgcmV0dXJuIG5hdmlnYXRvci5tYXhUb3VjaFBvaW50cyB8fCAoXCJvbnRvdWNoc3RhcnRcIiBpbiB0aGlzKTtcbn1cblxuZnVuY3Rpb24gZGVmYXVsdENvbnN0cmFpbih0cmFuc2Zvcm0sIGV4dGVudCwgdHJhbnNsYXRlRXh0ZW50KSB7XG4gIHZhciBkeDAgPSB0cmFuc2Zvcm0uaW52ZXJ0WChleHRlbnRbMF1bMF0pIC0gdHJhbnNsYXRlRXh0ZW50WzBdWzBdLFxuICAgICAgZHgxID0gdHJhbnNmb3JtLmludmVydFgoZXh0ZW50WzFdWzBdKSAtIHRyYW5zbGF0ZUV4dGVudFsxXVswXSxcbiAgICAgIGR5MCA9IHRyYW5zZm9ybS5pbnZlcnRZKGV4dGVudFswXVsxXSkgLSB0cmFuc2xhdGVFeHRlbnRbMF1bMV0sXG4gICAgICBkeTEgPSB0cmFuc2Zvcm0uaW52ZXJ0WShleHRlbnRbMV1bMV0pIC0gdHJhbnNsYXRlRXh0ZW50WzFdWzFdO1xuICByZXR1cm4gdHJhbnNmb3JtLnRyYW5zbGF0ZShcbiAgICBkeDEgPiBkeDAgPyAoZHgwICsgZHgxKSAvIDIgOiBNYXRoLm1pbigwLCBkeDApIHx8IE1hdGgubWF4KDAsIGR4MSksXG4gICAgZHkxID4gZHkwID8gKGR5MCArIGR5MSkgLyAyIDogTWF0aC5taW4oMCwgZHkwKSB8fCBNYXRoLm1heCgwLCBkeTEpXG4gICk7XG59XG5cbmV4cG9ydCBkZWZhdWx0IGZ1bmN0aW9uKCkge1xuICB2YXIgZmlsdGVyID0gZGVmYXVsdEZpbHRlcixcbiAgICAgIGV4dGVudCA9IGRlZmF1bHRFeHRlbnQsXG4gICAgICBjb25zdHJhaW4gPSBkZWZhdWx0Q29uc3RyYWluLFxuICAgICAgd2hlZWxEZWx0YSA9IGRlZmF1bHRXaGVlbERlbHRhLFxuICAgICAgdG91Y2hhYmxlID0gZGVmYXVsdFRvdWNoYWJsZSxcbiAgICAgIHNjYWxlRXh0ZW50ID0gWzAsIEluZmluaXR5XSxcbiAgICAgIHRyYW5zbGF0ZUV4dGVudCA9IFtbLUluZmluaXR5LCAtSW5maW5pdHldLCBbSW5maW5pdHksIEluZmluaXR5XV0sXG4gICAgICBkdXJhdGlvbiA9IDI1MCxcbiAgICAgIGludGVycG9sYXRlID0gaW50ZXJwb2xhdGVab29tLFxuICAgICAgbGlzdGVuZXJzID0gZGlzcGF0Y2goXCJzdGFydFwiLCBcInpvb21cIiwgXCJlbmRcIiksXG4gICAgICB0b3VjaHN0YXJ0aW5nLFxuICAgICAgdG91Y2hmaXJzdCxcbiAgICAgIHRvdWNoZW5kaW5nLFxuICAgICAgdG91Y2hEZWxheSA9IDUwMCxcbiAgICAgIHdoZWVsRGVsYXkgPSAxNTAsXG4gICAgICBjbGlja0Rpc3RhbmNlMiA9IDAsXG4gICAgICB0YXBEaXN0YW5jZSA9IDEwO1xuXG4gIGZ1bmN0aW9uIHpvb20oc2VsZWN0aW9uKSB7XG4gICAgc2VsZWN0aW9uXG4gICAgICAgIC5wcm9wZXJ0eShcIl9fem9vbVwiLCBkZWZhdWx0VHJhbnNmb3JtKVxuICAgICAgICAub24oXCJ3aGVlbC56b29tXCIsIHdoZWVsZWQsIHtwYXNzaXZlOiBmYWxzZX0pXG4gICAgICAgIC5vbihcIm1vdXNlZG93bi56b29tXCIsIG1vdXNlZG93bmVkKVxuICAgICAgICAub24oXCJkYmxjbGljay56b29tXCIsIGRibGNsaWNrZWQpXG4gICAgICAuZmlsdGVyKHRvdWNoYWJsZSlcbiAgICAgICAgLm9uKFwidG91Y2hzdGFydC56b29tXCIsIHRvdWNoc3RhcnRlZClcbiAgICAgICAgLm9uKFwidG91Y2htb3ZlLnpvb21cIiwgdG91Y2htb3ZlZClcbiAgICAgICAgLm9uKFwidG91Y2hlbmQuem9vbSB0b3VjaGNhbmNlbC56b29tXCIsIHRvdWNoZW5kZWQpXG4gICAgICAgIC5zdHlsZShcIi13ZWJraXQtdGFwLWhpZ2hsaWdodC1jb2xvclwiLCBcInJnYmEoMCwwLDAsMClcIik7XG4gIH1cblxuICB6b29tLnRyYW5zZm9ybSA9IGZ1bmN0aW9uKGNvbGxlY3Rpb24sIHRyYW5zZm9ybSwgcG9pbnQsIGV2ZW50KSB7XG4gICAgdmFyIHNlbGVjdGlvbiA9IGNvbGxlY3Rpb24uc2VsZWN0aW9uID8gY29sbGVjdGlvbi5zZWxlY3Rpb24oKSA6IGNvbGxlY3Rpb247XG4gICAgc2VsZWN0aW9uLnByb3BlcnR5KFwiX196b29tXCIsIGRlZmF1bHRUcmFuc2Zvcm0pO1xuICAgIGlmIChjb2xsZWN0aW9uICE9PSBzZWxlY3Rpb24pIHtcbiAgICAgIHNjaGVkdWxlKGNvbGxlY3Rpb24sIHRyYW5zZm9ybSwgcG9pbnQsIGV2ZW50KTtcbiAgICB9IGVsc2Uge1xuICAgICAgc2VsZWN0aW9uLmludGVycnVwdCgpLmVhY2goZnVuY3Rpb24oKSB7XG4gICAgICAgIGdlc3R1cmUodGhpcywgYXJndW1lbnRzKVxuICAgICAgICAgIC5ldmVudChldmVudClcbiAgICAgICAgICAuc3RhcnQoKVxuICAgICAgICAgIC56b29tKG51bGwsIHR5cGVvZiB0cmFuc2Zvcm0gPT09IFwiZnVuY3Rpb25cIiA/IHRyYW5zZm9ybS5hcHBseSh0aGlzLCBhcmd1bWVudHMpIDogdHJhbnNmb3JtKVxuICAgICAgICAgIC5lbmQoKTtcbiAgICAgIH0pO1xuICAgIH1cbiAgfTtcblxuICB6b29tLnNjYWxlQnkgPSBmdW5jdGlvbihzZWxlY3Rpb24sIGssIHAsIGV2ZW50KSB7XG4gICAgem9vbS5zY2FsZVRvKHNlbGVjdGlvbiwgZnVuY3Rpb24oKSB7XG4gICAgICB2YXIgazAgPSB0aGlzLl9fem9vbS5rLFxuICAgICAgICAgIGsxID0gdHlwZW9mIGsgPT09IFwiZnVuY3Rpb25cIiA/IGsuYXBwbHkodGhpcywgYXJndW1lbnRzKSA6IGs7XG4gICAgICByZXR1cm4gazAgKiBrMTtcbiAgICB9LCBwLCBldmVudCk7XG4gIH07XG5cbiAgem9vbS5zY2FsZVRvID0gZnVuY3Rpb24oc2VsZWN0aW9uLCBrLCBwLCBldmVudCkge1xuICAgIHpvb20udHJhbnNmb3JtKHNlbGVjdGlvbiwgZnVuY3Rpb24oKSB7XG4gICAgICB2YXIgZSA9IGV4dGVudC5hcHBseSh0aGlzLCBhcmd1bWVudHMpLFxuICAgICAgICAgIHQwID0gdGhpcy5fX3pvb20sXG4gICAgICAgICAgcDAgPSBwID09IG51bGwgPyBjZW50cm9pZChlKSA6IHR5cGVvZiBwID09PSBcImZ1bmN0aW9uXCIgPyBwLmFwcGx5KHRoaXMsIGFyZ3VtZW50cykgOiBwLFxuICAgICAgICAgIHAxID0gdDAuaW52ZXJ0KHAwKSxcbiAgICAgICAgICBrMSA9IHR5cGVvZiBrID09PSBcImZ1bmN0aW9uXCIgPyBrLmFwcGx5KHRoaXMsIGFyZ3VtZW50cykgOiBrO1xuICAgICAgcmV0dXJuIGNvbnN0cmFpbih0cmFuc2xhdGUoc2NhbGUodDAsIGsxKSwgcDAsIHAxKSwgZSwgdHJhbnNsYXRlRXh0ZW50KTtcbiAgICB9LCBwLCBldmVudCk7XG4gIH07XG5cbiAgem9vbS50cmFuc2xhdGVCeSA9IGZ1bmN0aW9uKHNlbGVjdGlvbiwgeCwgeSwgZXZlbnQpIHtcbiAgICB6b29tLnRyYW5zZm9ybShzZWxlY3Rpb24sIGZ1bmN0aW9uKCkge1xuICAgICAgcmV0dXJuIGNvbnN0cmFpbih0aGlzLl9fem9vbS50cmFuc2xhdGUoXG4gICAgICAgIHR5cGVvZiB4ID09PSBcImZ1bmN0aW9uXCIgPyB4LmFwcGx5KHRoaXMsIGFyZ3VtZW50cykgOiB4LFxuICAgICAgICB0eXBlb2YgeSA9PT0gXCJmdW5jdGlvblwiID8geS5hcHBseSh0aGlzLCBhcmd1bWVudHMpIDogeVxuICAgICAgKSwgZXh0ZW50LmFwcGx5KHRoaXMsIGFyZ3VtZW50cyksIHRyYW5zbGF0ZUV4dGVudCk7XG4gICAgfSwgbnVsbCwgZXZlbnQpO1xuICB9O1xuXG4gIHpvb20udHJhbnNsYXRlVG8gPSBmdW5jdGlvbihzZWxlY3Rpb24sIHgsIHksIHAsIGV2ZW50KSB7XG4gICAgem9vbS50cmFuc2Zvcm0oc2VsZWN0aW9uLCBmdW5jdGlvbigpIHtcbiAgICAgIHZhciBlID0gZXh0ZW50LmFwcGx5KHRoaXMsIGFyZ3VtZW50cyksXG4gICAgICAgICAgdCA9IHRoaXMuX196b29tLFxuICAgICAgICAgIHAwID0gcCA9PSBudWxsID8gY2VudHJvaWQoZSkgOiB0eXBlb2YgcCA9PT0gXCJmdW5jdGlvblwiID8gcC5hcHBseSh0aGlzLCBhcmd1bWVudHMpIDogcDtcbiAgICAgIHJldHVybiBjb25zdHJhaW4oaWRlbnRpdHkudHJhbnNsYXRlKHAwWzBdLCBwMFsxXSkuc2NhbGUodC5rKS50cmFuc2xhdGUoXG4gICAgICAgIHR5cGVvZiB4ID09PSBcImZ1bmN0aW9uXCIgPyAteC5hcHBseSh0aGlzLCBhcmd1bWVudHMpIDogLXgsXG4gICAgICAgIHR5cGVvZiB5ID09PSBcImZ1bmN0aW9uXCIgPyAteS5hcHBseSh0aGlzLCBhcmd1bWVudHMpIDogLXlcbiAgICAgICksIGUsIHRyYW5zbGF0ZUV4dGVudCk7XG4gICAgfSwgcCwgZXZlbnQpO1xuICB9O1xuXG4gIGZ1bmN0aW9uIHNjYWxlKHRyYW5zZm9ybSwgaykge1xuICAgIGsgPSBNYXRoLm1heChzY2FsZUV4dGVudFswXSwgTWF0aC5taW4oc2NhbGVFeHRlbnRbMV0sIGspKTtcbiAgICByZXR1cm4gayA9PT0gdHJhbnNmb3JtLmsgPyB0cmFuc2Zvcm0gOiBuZXcgVHJhbnNmb3JtKGssIHRyYW5zZm9ybS54LCB0cmFuc2Zvcm0ueSk7XG4gIH1cblxuICBmdW5jdGlvbiB0cmFuc2xhdGUodHJhbnNmb3JtLCBwMCwgcDEpIHtcbiAgICB2YXIgeCA9IHAwWzBdIC0gcDFbMF0gKiB0cmFuc2Zvcm0uaywgeSA9IHAwWzFdIC0gcDFbMV0gKiB0cmFuc2Zvcm0uaztcbiAgICByZXR1cm4geCA9PT0gdHJhbnNmb3JtLnggJiYgeSA9PT0gdHJhbnNmb3JtLnkgPyB0cmFuc2Zvcm0gOiBuZXcgVHJhbnNmb3JtKHRyYW5zZm9ybS5rLCB4LCB5KTtcbiAgfVxuXG4gIGZ1bmN0aW9uIGNlbnRyb2lkKGV4dGVudCkge1xuICAgIHJldHVybiBbKCtleHRlbnRbMF1bMF0gKyArZXh0ZW50WzFdWzBdKSAvIDIsICgrZXh0ZW50WzBdWzFdICsgK2V4dGVudFsxXVsxXSkgLyAyXTtcbiAgfVxuXG4gIGZ1bmN0aW9uIHNjaGVkdWxlKHRyYW5zaXRpb24sIHRyYW5zZm9ybSwgcG9pbnQsIGV2ZW50KSB7XG4gICAgdHJhbnNpdGlvblxuICAgICAgICAub24oXCJzdGFydC56b29tXCIsIGZ1bmN0aW9uKCkgeyBnZXN0dXJlKHRoaXMsIGFyZ3VtZW50cykuZXZlbnQoZXZlbnQpLnN0YXJ0KCk7IH0pXG4gICAgICAgIC5vbihcImludGVycnVwdC56b29tIGVuZC56b29tXCIsIGZ1bmN0aW9uKCkgeyBnZXN0dXJlKHRoaXMsIGFyZ3VtZW50cykuZXZlbnQoZXZlbnQpLmVuZCgpOyB9KVxuICAgICAgICAudHdlZW4oXCJ6b29tXCIsIGZ1bmN0aW9uKCkge1xuICAgICAgICAgIHZhciB0aGF0ID0gdGhpcyxcbiAgICAgICAgICAgICAgYXJncyA9IGFyZ3VtZW50cyxcbiAgICAgICAgICAgICAgZyA9IGdlc3R1cmUodGhhdCwgYXJncykuZXZlbnQoZXZlbnQpLFxuICAgICAgICAgICAgICBlID0gZXh0ZW50LmFwcGx5KHRoYXQsIGFyZ3MpLFxuICAgICAgICAgICAgICBwID0gcG9pbnQgPT0gbnVsbCA/IGNlbnRyb2lkKGUpIDogdHlwZW9mIHBvaW50ID09PSBcImZ1bmN0aW9uXCIgPyBwb2ludC5hcHBseSh0aGF0LCBhcmdzKSA6IHBvaW50LFxuICAgICAgICAgICAgICB3ID0gTWF0aC5tYXgoZVsxXVswXSAtIGVbMF1bMF0sIGVbMV1bMV0gLSBlWzBdWzFdKSxcbiAgICAgICAgICAgICAgYSA9IHRoYXQuX196b29tLFxuICAgICAgICAgICAgICBiID0gdHlwZW9mIHRyYW5zZm9ybSA9PT0gXCJmdW5jdGlvblwiID8gdHJhbnNmb3JtLmFwcGx5KHRoYXQsIGFyZ3MpIDogdHJhbnNmb3JtLFxuICAgICAgICAgICAgICBpID0gaW50ZXJwb2xhdGUoYS5pbnZlcnQocCkuY29uY2F0KHcgLyBhLmspLCBiLmludmVydChwKS5jb25jYXQodyAvIGIuaykpO1xuICAgICAgICAgIHJldHVybiBmdW5jdGlvbih0KSB7XG4gICAgICAgICAgICBpZiAodCA9PT0gMSkgdCA9IGI7IC8vIEF2b2lkIHJvdW5kaW5nIGVycm9yIG9uIGVuZC5cbiAgICAgICAgICAgIGVsc2UgeyB2YXIgbCA9IGkodCksIGsgPSB3IC8gbFsyXTsgdCA9IG5ldyBUcmFuc2Zvcm0oaywgcFswXSAtIGxbMF0gKiBrLCBwWzFdIC0gbFsxXSAqIGspOyB9XG4gICAgICAgICAgICBnLnpvb20obnVsbCwgdCk7XG4gICAgICAgICAgfTtcbiAgICAgICAgfSk7XG4gIH1cblxuICBmdW5jdGlvbiBnZXN0dXJlKHRoYXQsIGFyZ3MsIGNsZWFuKSB7XG4gICAgcmV0dXJuICghY2xlYW4gJiYgdGhhdC5fX3pvb21pbmcpIHx8IG5ldyBHZXN0dXJlKHRoYXQsIGFyZ3MpO1xuICB9XG5cbiAgZnVuY3Rpb24gR2VzdHVyZSh0aGF0LCBhcmdzKSB7XG4gICAgdGhpcy50aGF0ID0gdGhhdDtcbiAgICB0aGlzLmFyZ3MgPSBhcmdzO1xuICAgIHRoaXMuYWN0aXZlID0gMDtcbiAgICB0aGlzLnNvdXJjZUV2ZW50ID0gbnVsbDtcbiAgICB0aGlzLmV4dGVudCA9IGV4dGVudC5hcHBseSh0aGF0LCBhcmdzKTtcbiAgICB0aGlzLnRhcHMgPSAwO1xuICB9XG5cbiAgR2VzdHVyZS5wcm90b3R5cGUgPSB7XG4gICAgZXZlbnQ6IGZ1bmN0aW9uKGV2ZW50KSB7XG4gICAgICBpZiAoZXZlbnQpIHRoaXMuc291cmNlRXZlbnQgPSBldmVudDtcbiAgICAgIHJldHVybiB0aGlzO1xuICAgIH0sXG4gICAgc3RhcnQ6IGZ1bmN0aW9uKCkge1xuICAgICAgaWYgKCsrdGhpcy5hY3RpdmUgPT09IDEpIHtcbiAgICAgICAgdGhpcy50aGF0Ll9fem9vbWluZyA9IHRoaXM7XG4gICAgICAgIHRoaXMuZW1pdChcInN0YXJ0XCIpO1xuICAgICAgfVxuICAgICAgcmV0dXJuIHRoaXM7XG4gICAgfSxcbiAgICB6b29tOiBmdW5jdGlvbihrZXksIHRyYW5zZm9ybSkge1xuICAgICAgaWYgKHRoaXMubW91c2UgJiYga2V5ICE9PSBcIm1vdXNlXCIpIHRoaXMubW91c2VbMV0gPSB0cmFuc2Zvcm0uaW52ZXJ0KHRoaXMubW91c2VbMF0pO1xuICAgICAgaWYgKHRoaXMudG91Y2gwICYmIGtleSAhPT0gXCJ0b3VjaFwiKSB0aGlzLnRvdWNoMFsxXSA9IHRyYW5zZm9ybS5pbnZlcnQodGhpcy50b3VjaDBbMF0pO1xuICAgICAgaWYgKHRoaXMudG91Y2gxICYmIGtleSAhPT0gXCJ0b3VjaFwiKSB0aGlzLnRvdWNoMVsxXSA9IHRyYW5zZm9ybS5pbnZlcnQodGhpcy50b3VjaDFbMF0pO1xuICAgICAgdGhpcy50aGF0Ll9fem9vbSA9IHRyYW5zZm9ybTtcbiAgICAgIHRoaXMuZW1pdChcInpvb21cIik7XG4gICAgICByZXR1cm4gdGhpcztcbiAgICB9LFxuICAgIGVuZDogZnVuY3Rpb24oKSB7XG4gICAgICBpZiAoLS10aGlzLmFjdGl2ZSA9PT0gMCkge1xuICAgICAgICBkZWxldGUgdGhpcy50aGF0Ll9fem9vbWluZztcbiAgICAgICAgdGhpcy5lbWl0KFwiZW5kXCIpO1xuICAgICAgfVxuICAgICAgcmV0dXJuIHRoaXM7XG4gICAgfSxcbiAgICBlbWl0OiBmdW5jdGlvbih0eXBlKSB7XG4gICAgICB2YXIgZCA9IHNlbGVjdCh0aGlzLnRoYXQpLmRhdHVtKCk7XG4gICAgICBsaXN0ZW5lcnMuY2FsbChcbiAgICAgICAgdHlwZSxcbiAgICAgICAgdGhpcy50aGF0LFxuICAgICAgICBuZXcgWm9vbUV2ZW50KHR5cGUsIHtcbiAgICAgICAgICBzb3VyY2VFdmVudDogdGhpcy5zb3VyY2VFdmVudCxcbiAgICAgICAgICB0YXJnZXQ6IHpvb20sXG4gICAgICAgICAgdHlwZSxcbiAgICAgICAgICB0cmFuc2Zvcm06IHRoaXMudGhhdC5fX3pvb20sXG4gICAgICAgICAgZGlzcGF0Y2g6IGxpc3RlbmVyc1xuICAgICAgICB9KSxcbiAgICAgICAgZFxuICAgICAgKTtcbiAgICB9XG4gIH07XG5cbiAgZnVuY3Rpb24gd2hlZWxlZChldmVudCwgLi4uYXJncykge1xuICAgIGlmICghZmlsdGVyLmFwcGx5KHRoaXMsIGFyZ3VtZW50cykpIHJldHVybjtcbiAgICB2YXIgZyA9IGdlc3R1cmUodGhpcywgYXJncykuZXZlbnQoZXZlbnQpLFxuICAgICAgICB0ID0gdGhpcy5fX3pvb20sXG4gICAgICAgIGsgPSBNYXRoLm1heChzY2FsZUV4dGVudFswXSwgTWF0aC5taW4oc2NhbGVFeHRlbnRbMV0sIHQuayAqIE1hdGgucG93KDIsIHdoZWVsRGVsdGEuYXBwbHkodGhpcywgYXJndW1lbnRzKSkpKSxcbiAgICAgICAgcCA9IHBvaW50ZXIoZXZlbnQpO1xuXG4gICAgLy8gSWYgdGhlIG1vdXNlIGlzIGluIHRoZSBzYW1lIGxvY2F0aW9uIGFzIGJlZm9yZSwgcmV1c2UgaXQuXG4gICAgLy8gSWYgdGhlcmUgd2VyZSByZWNlbnQgd2hlZWwgZXZlbnRzLCByZXNldCB0aGUgd2hlZWwgaWRsZSB0aW1lb3V0LlxuICAgIGlmIChnLndoZWVsKSB7XG4gICAgICBpZiAoZy5tb3VzZVswXVswXSAhPT0gcFswXSB8fCBnLm1vdXNlWzBdWzFdICE9PSBwWzFdKSB7XG4gICAgICAgIGcubW91c2VbMV0gPSB0LmludmVydChnLm1vdXNlWzBdID0gcCk7XG4gICAgICB9XG4gICAgICBjbGVhclRpbWVvdXQoZy53aGVlbCk7XG4gICAgfVxuXG4gICAgLy8gSWYgdGhpcyB3aGVlbCBldmVudCB3b27igJl0IHRyaWdnZXIgYSB0cmFuc2Zvcm0gY2hhbmdlLCBpZ25vcmUgaXQuXG4gICAgZWxzZSBpZiAodC5rID09PSBrKSByZXR1cm47XG5cbiAgICAvLyBPdGhlcndpc2UsIGNhcHR1cmUgdGhlIG1vdXNlIHBvaW50IGFuZCBsb2NhdGlvbiBhdCB0aGUgc3RhcnQuXG4gICAgZWxzZSB7XG4gICAgICBnLm1vdXNlID0gW3AsIHQuaW52ZXJ0KHApXTtcbiAgICAgIGludGVycnVwdCh0aGlzKTtcbiAgICAgIGcuc3RhcnQoKTtcbiAgICB9XG5cbiAgICBub2V2ZW50KGV2ZW50KTtcbiAgICBnLndoZWVsID0gc2V0VGltZW91dCh3aGVlbGlkbGVkLCB3aGVlbERlbGF5KTtcbiAgICBnLnpvb20oXCJtb3VzZVwiLCBjb25zdHJhaW4odHJhbnNsYXRlKHNjYWxlKHQsIGspLCBnLm1vdXNlWzBdLCBnLm1vdXNlWzFdKSwgZy5leHRlbnQsIHRyYW5zbGF0ZUV4dGVudCkpO1xuXG4gICAgZnVuY3Rpb24gd2hlZWxpZGxlZCgpIHtcbiAgICAgIGcud2hlZWwgPSBudWxsO1xuICAgICAgZy5lbmQoKTtcbiAgICB9XG4gIH1cblxuICBmdW5jdGlvbiBtb3VzZWRvd25lZChldmVudCwgLi4uYXJncykge1xuICAgIGlmICh0b3VjaGVuZGluZyB8fCAhZmlsdGVyLmFwcGx5KHRoaXMsIGFyZ3VtZW50cykpIHJldHVybjtcbiAgICB2YXIgY3VycmVudFRhcmdldCA9IGV2ZW50LmN1cnJlbnRUYXJnZXQsXG4gICAgICAgIGcgPSBnZXN0dXJlKHRoaXMsIGFyZ3MsIHRydWUpLmV2ZW50KGV2ZW50KSxcbiAgICAgICAgdiA9IHNlbGVjdChldmVudC52aWV3KS5vbihcIm1vdXNlbW92ZS56b29tXCIsIG1vdXNlbW92ZWQsIHRydWUpLm9uKFwibW91c2V1cC56b29tXCIsIG1vdXNldXBwZWQsIHRydWUpLFxuICAgICAgICBwID0gcG9pbnRlcihldmVudCwgY3VycmVudFRhcmdldCksXG4gICAgICAgIHgwID0gZXZlbnQuY2xpZW50WCxcbiAgICAgICAgeTAgPSBldmVudC5jbGllbnRZO1xuXG4gICAgZHJhZ0Rpc2FibGUoZXZlbnQudmlldyk7XG4gICAgbm9wcm9wYWdhdGlvbihldmVudCk7XG4gICAgZy5tb3VzZSA9IFtwLCB0aGlzLl9fem9vbS5pbnZlcnQocCldO1xuICAgIGludGVycnVwdCh0aGlzKTtcbiAgICBnLnN0YXJ0KCk7XG5cbiAgICBmdW5jdGlvbiBtb3VzZW1vdmVkKGV2ZW50KSB7XG4gICAgICBub2V2ZW50KGV2ZW50KTtcbiAgICAgIGlmICghZy5tb3ZlZCkge1xuICAgICAgICB2YXIgZHggPSBldmVudC5jbGllbnRYIC0geDAsIGR5ID0gZXZlbnQuY2xpZW50WSAtIHkwO1xuICAgICAgICBnLm1vdmVkID0gZHggKiBkeCArIGR5ICogZHkgPiBjbGlja0Rpc3RhbmNlMjtcbiAgICAgIH1cbiAgICAgIGcuZXZlbnQoZXZlbnQpXG4gICAgICAgLnpvb20oXCJtb3VzZVwiLCBjb25zdHJhaW4odHJhbnNsYXRlKGcudGhhdC5fX3pvb20sIGcubW91c2VbMF0gPSBwb2ludGVyKGV2ZW50LCBjdXJyZW50VGFyZ2V0KSwgZy5tb3VzZVsxXSksIGcuZXh0ZW50LCB0cmFuc2xhdGVFeHRlbnQpKTtcbiAgICB9XG5cbiAgICBmdW5jdGlvbiBtb3VzZXVwcGVkKGV2ZW50KSB7XG4gICAgICB2Lm9uKFwibW91c2Vtb3ZlLnpvb20gbW91c2V1cC56b29tXCIsIG51bGwpO1xuICAgICAgZHJhZ0VuYWJsZShldmVudC52aWV3LCBnLm1vdmVkKTtcbiAgICAgIG5vZXZlbnQoZXZlbnQpO1xuICAgICAgZy5ldmVudChldmVudCkuZW5kKCk7XG4gICAgfVxuICB9XG5cbiAgZnVuY3Rpb24gZGJsY2xpY2tlZChldmVudCwgLi4uYXJncykge1xuICAgIGlmICghZmlsdGVyLmFwcGx5KHRoaXMsIGFyZ3VtZW50cykpIHJldHVybjtcbiAgICB2YXIgdDAgPSB0aGlzLl9fem9vbSxcbiAgICAgICAgcDAgPSBwb2ludGVyKGV2ZW50LmNoYW5nZWRUb3VjaGVzID8gZXZlbnQuY2hhbmdlZFRvdWNoZXNbMF0gOiBldmVudCwgdGhpcyksXG4gICAgICAgIHAxID0gdDAuaW52ZXJ0KHAwKSxcbiAgICAgICAgazEgPSB0MC5rICogKGV2ZW50LnNoaWZ0S2V5ID8gMC41IDogMiksXG4gICAgICAgIHQxID0gY29uc3RyYWluKHRyYW5zbGF0ZShzY2FsZSh0MCwgazEpLCBwMCwgcDEpLCBleHRlbnQuYXBwbHkodGhpcywgYXJncyksIHRyYW5zbGF0ZUV4dGVudCk7XG5cbiAgICBub2V2ZW50KGV2ZW50KTtcbiAgICBpZiAoZHVyYXRpb24gPiAwKSBzZWxlY3QodGhpcykudHJhbnNpdGlvbigpLmR1cmF0aW9uKGR1cmF0aW9uKS5jYWxsKHNjaGVkdWxlLCB0MSwgcDAsIGV2ZW50KTtcbiAgICBlbHNlIHNlbGVjdCh0aGlzKS5jYWxsKHpvb20udHJhbnNmb3JtLCB0MSwgcDAsIGV2ZW50KTtcbiAgfVxuXG4gIGZ1bmN0aW9uIHRvdWNoc3RhcnRlZChldmVudCwgLi4uYXJncykge1xuICAgIGlmICghZmlsdGVyLmFwcGx5KHRoaXMsIGFyZ3VtZW50cykpIHJldHVybjtcbiAgICB2YXIgdG91Y2hlcyA9IGV2ZW50LnRvdWNoZXMsXG4gICAgICAgIG4gPSB0b3VjaGVzLmxlbmd0aCxcbiAgICAgICAgZyA9IGdlc3R1cmUodGhpcywgYXJncywgZXZlbnQuY2hhbmdlZFRvdWNoZXMubGVuZ3RoID09PSBuKS5ldmVudChldmVudCksXG4gICAgICAgIHN0YXJ0ZWQsIGksIHQsIHA7XG5cbiAgICBub3Byb3BhZ2F0aW9uKGV2ZW50KTtcbiAgICBmb3IgKGkgPSAwOyBpIDwgbjsgKytpKSB7XG4gICAgICB0ID0gdG91Y2hlc1tpXSwgcCA9IHBvaW50ZXIodCwgdGhpcyk7XG4gICAgICBwID0gW3AsIHRoaXMuX196b29tLmludmVydChwKSwgdC5pZGVudGlmaWVyXTtcbiAgICAgIGlmICghZy50b3VjaDApIGcudG91Y2gwID0gcCwgc3RhcnRlZCA9IHRydWUsIGcudGFwcyA9IDEgKyAhIXRvdWNoc3RhcnRpbmc7XG4gICAgICBlbHNlIGlmICghZy50b3VjaDEgJiYgZy50b3VjaDBbMl0gIT09IHBbMl0pIGcudG91Y2gxID0gcCwgZy50YXBzID0gMDtcbiAgICB9XG5cbiAgICBpZiAodG91Y2hzdGFydGluZykgdG91Y2hzdGFydGluZyA9IGNsZWFyVGltZW91dCh0b3VjaHN0YXJ0aW5nKTtcblxuICAgIGlmIChzdGFydGVkKSB7XG4gICAgICBpZiAoZy50YXBzIDwgMikgdG91Y2hmaXJzdCA9IHBbMF0sIHRvdWNoc3RhcnRpbmcgPSBzZXRUaW1lb3V0KGZ1bmN0aW9uKCkgeyB0b3VjaHN0YXJ0aW5nID0gbnVsbDsgfSwgdG91Y2hEZWxheSk7XG4gICAgICBpbnRlcnJ1cHQodGhpcyk7XG4gICAgICBnLnN0YXJ0KCk7XG4gICAgfVxuICB9XG5cbiAgZnVuY3Rpb24gdG91Y2htb3ZlZChldmVudCwgLi4uYXJncykge1xuICAgIGlmICghdGhpcy5fX3pvb21pbmcpIHJldHVybjtcbiAgICB2YXIgZyA9IGdlc3R1cmUodGhpcywgYXJncykuZXZlbnQoZXZlbnQpLFxuICAgICAgICB0b3VjaGVzID0gZXZlbnQuY2hhbmdlZFRvdWNoZXMsXG4gICAgICAgIG4gPSB0b3VjaGVzLmxlbmd0aCwgaSwgdCwgcCwgbDtcblxuICAgIG5vZXZlbnQoZXZlbnQpO1xuICAgIGZvciAoaSA9IDA7IGkgPCBuOyArK2kpIHtcbiAgICAgIHQgPSB0b3VjaGVzW2ldLCBwID0gcG9pbnRlcih0LCB0aGlzKTtcbiAgICAgIGlmIChnLnRvdWNoMCAmJiBnLnRvdWNoMFsyXSA9PT0gdC5pZGVudGlmaWVyKSBnLnRvdWNoMFswXSA9IHA7XG4gICAgICBlbHNlIGlmIChnLnRvdWNoMSAmJiBnLnRvdWNoMVsyXSA9PT0gdC5pZGVudGlmaWVyKSBnLnRvdWNoMVswXSA9IHA7XG4gICAgfVxuICAgIHQgPSBnLnRoYXQuX196b29tO1xuICAgIGlmIChnLnRvdWNoMSkge1xuICAgICAgdmFyIHAwID0gZy50b3VjaDBbMF0sIGwwID0gZy50b3VjaDBbMV0sXG4gICAgICAgICAgcDEgPSBnLnRvdWNoMVswXSwgbDEgPSBnLnRvdWNoMVsxXSxcbiAgICAgICAgICBkcCA9IChkcCA9IHAxWzBdIC0gcDBbMF0pICogZHAgKyAoZHAgPSBwMVsxXSAtIHAwWzFdKSAqIGRwLFxuICAgICAgICAgIGRsID0gKGRsID0gbDFbMF0gLSBsMFswXSkgKiBkbCArIChkbCA9IGwxWzFdIC0gbDBbMV0pICogZGw7XG4gICAgICB0ID0gc2NhbGUodCwgTWF0aC5zcXJ0KGRwIC8gZGwpKTtcbiAgICAgIHAgPSBbKHAwWzBdICsgcDFbMF0pIC8gMiwgKHAwWzFdICsgcDFbMV0pIC8gMl07XG4gICAgICBsID0gWyhsMFswXSArIGwxWzBdKSAvIDIsIChsMFsxXSArIGwxWzFdKSAvIDJdO1xuICAgIH1cbiAgICBlbHNlIGlmIChnLnRvdWNoMCkgcCA9IGcudG91Y2gwWzBdLCBsID0gZy50b3VjaDBbMV07XG4gICAgZWxzZSByZXR1cm47XG5cbiAgICBnLnpvb20oXCJ0b3VjaFwiLCBjb25zdHJhaW4odHJhbnNsYXRlKHQsIHAsIGwpLCBnLmV4dGVudCwgdHJhbnNsYXRlRXh0ZW50KSk7XG4gIH1cblxuICBmdW5jdGlvbiB0b3VjaGVuZGVkKGV2ZW50LCAuLi5hcmdzKSB7XG4gICAgaWYgKCF0aGlzLl9fem9vbWluZykgcmV0dXJuO1xuICAgIHZhciBnID0gZ2VzdHVyZSh0aGlzLCBhcmdzKS5ldmVudChldmVudCksXG4gICAgICAgIHRvdWNoZXMgPSBldmVudC5jaGFuZ2VkVG91Y2hlcyxcbiAgICAgICAgbiA9IHRvdWNoZXMubGVuZ3RoLCBpLCB0O1xuXG4gICAgbm9wcm9wYWdhdGlvbihldmVudCk7XG4gICAgaWYgKHRvdWNoZW5kaW5nKSBjbGVhclRpbWVvdXQodG91Y2hlbmRpbmcpO1xuICAgIHRvdWNoZW5kaW5nID0gc2V0VGltZW91dChmdW5jdGlvbigpIHsgdG91Y2hlbmRpbmcgPSBudWxsOyB9LCB0b3VjaERlbGF5KTtcbiAgICBmb3IgKGkgPSAwOyBpIDwgbjsgKytpKSB7XG4gICAgICB0ID0gdG91Y2hlc1tpXTtcbiAgICAgIGlmIChnLnRvdWNoMCAmJiBnLnRvdWNoMFsyXSA9PT0gdC5pZGVudGlmaWVyKSBkZWxldGUgZy50b3VjaDA7XG4gICAgICBlbHNlIGlmIChnLnRvdWNoMSAmJiBnLnRvdWNoMVsyXSA9PT0gdC5pZGVudGlmaWVyKSBkZWxldGUgZy50b3VjaDE7XG4gICAgfVxuICAgIGlmIChnLnRvdWNoMSAmJiAhZy50b3VjaDApIGcudG91Y2gwID0gZy50b3VjaDEsIGRlbGV0ZSBnLnRvdWNoMTtcbiAgICBpZiAoZy50b3VjaDApIGcudG91Y2gwWzFdID0gdGhpcy5fX3pvb20uaW52ZXJ0KGcudG91Y2gwWzBdKTtcbiAgICBlbHNlIHtcbiAgICAgIGcuZW5kKCk7XG4gICAgICAvLyBJZiB0aGlzIHdhcyBhIGRibHRhcCwgcmVyb3V0ZSB0byB0aGUgKG9wdGlvbmFsKSBkYmxjbGljay56b29tIGhhbmRsZXIuXG4gICAgICBpZiAoZy50YXBzID09PSAyKSB7XG4gICAgICAgIHQgPSBwb2ludGVyKHQsIHRoaXMpO1xuICAgICAgICBpZiAoTWF0aC5oeXBvdCh0b3VjaGZpcnN0WzBdIC0gdFswXSwgdG91Y2hmaXJzdFsxXSAtIHRbMV0pIDwgdGFwRGlzdGFuY2UpIHtcbiAgICAgICAgICB2YXIgcCA9IHNlbGVjdCh0aGlzKS5vbihcImRibGNsaWNrLnpvb21cIik7XG4gICAgICAgICAgaWYgKHApIHAuYXBwbHkodGhpcywgYXJndW1lbnRzKTtcbiAgICAgICAgfVxuICAgICAgfVxuICAgIH1cbiAgfVxuXG4gIHpvb20ud2hlZWxEZWx0YSA9IGZ1bmN0aW9uKF8pIHtcbiAgICByZXR1cm4gYXJndW1lbnRzLmxlbmd0aCA/ICh3aGVlbERlbHRhID0gdHlwZW9mIF8gPT09IFwiZnVuY3Rpb25cIiA/IF8gOiBjb25zdGFudCgrXyksIHpvb20pIDogd2hlZWxEZWx0YTtcbiAgfTtcblxuICB6b29tLmZpbHRlciA9IGZ1bmN0aW9uKF8pIHtcbiAgICByZXR1cm4gYXJndW1lbnRzLmxlbmd0aCA/IChmaWx0ZXIgPSB0eXBlb2YgXyA9PT0gXCJmdW5jdGlvblwiID8gXyA6IGNvbnN0YW50KCEhXyksIHpvb20pIDogZmlsdGVyO1xuICB9O1xuXG4gIHpvb20udG91Y2hhYmxlID0gZnVuY3Rpb24oXykge1xuICAgIHJldHVybiBhcmd1bWVudHMubGVuZ3RoID8gKHRvdWNoYWJsZSA9IHR5cGVvZiBfID09PSBcImZ1bmN0aW9uXCIgPyBfIDogY29uc3RhbnQoISFfKSwgem9vbSkgOiB0b3VjaGFibGU7XG4gIH07XG5cbiAgem9vbS5leHRlbnQgPSBmdW5jdGlvbihfKSB7XG4gICAgcmV0dXJuIGFyZ3VtZW50cy5sZW5ndGggPyAoZXh0ZW50ID0gdHlwZW9mIF8gPT09IFwiZnVuY3Rpb25cIiA/IF8gOiBjb25zdGFudChbWytfWzBdWzBdLCArX1swXVsxXV0sIFsrX1sxXVswXSwgK19bMV1bMV1dXSksIHpvb20pIDogZXh0ZW50O1xuICB9O1xuXG4gIHpvb20uc2NhbGVFeHRlbnQgPSBmdW5jdGlvbihfKSB7XG4gICAgcmV0dXJuIGFyZ3VtZW50cy5sZW5ndGggPyAoc2NhbGVFeHRlbnRbMF0gPSArX1swXSwgc2NhbGVFeHRlbnRbMV0gPSArX1sxXSwgem9vbSkgOiBbc2NhbGVFeHRlbnRbMF0sIHNjYWxlRXh0ZW50WzFdXTtcbiAgfTtcblxuICB6b29tLnRyYW5zbGF0ZUV4dGVudCA9IGZ1bmN0aW9uKF8pIHtcbiAgICByZXR1cm4gYXJndW1lbnRzLmxlbmd0aCA/ICh0cmFuc2xhdGVFeHRlbnRbMF1bMF0gPSArX1swXVswXSwgdHJhbnNsYXRlRXh0ZW50WzFdWzBdID0gK19bMV1bMF0sIHRyYW5zbGF0ZUV4dGVudFswXVsxXSA9ICtfWzBdWzFdLCB0cmFuc2xhdGVFeHRlbnRbMV1bMV0gPSArX1sxXVsxXSwgem9vbSkgOiBbW3RyYW5zbGF0ZUV4dGVudFswXVswXSwgdHJhbnNsYXRlRXh0ZW50WzBdWzFdXSwgW3RyYW5zbGF0ZUV4dGVudFsxXVswXSwgdHJhbnNsYXRlRXh0ZW50WzFdWzFdXV07XG4gIH07XG5cbiAgem9vbS5jb25zdHJhaW4gPSBmdW5jdGlvbihfKSB7XG4gICAgcmV0dXJuIGFyZ3VtZW50cy5sZW5ndGggPyAoY29uc3RyYWluID0gXywgem9vbSkgOiBjb25zdHJhaW47XG4gIH07XG5cbiAgem9vbS5kdXJhdGlvbiA9IGZ1bmN0aW9uKF8pIHtcbiAgICByZXR1cm4gYXJndW1lbnRzLmxlbmd0aCA/IChkdXJhdGlvbiA9ICtfLCB6b29tKSA6IGR1cmF0aW9uO1xuICB9O1xuXG4gIHpvb20uaW50ZXJwb2xhdGUgPSBmdW5jdGlvbihfKSB7XG4gICAgcmV0dXJuIGFyZ3VtZW50cy5sZW5ndGggPyAoaW50ZXJwb2xhdGUgPSBfLCB6b29tKSA6IGludGVycG9sYXRlO1xuICB9O1xuXG4gIHpvb20ub24gPSBmdW5jdGlvbigpIHtcbiAgICB2YXIgdmFsdWUgPSBsaXN0ZW5lcnMub24uYXBwbHkobGlzdGVuZXJzLCBhcmd1bWVudHMpO1xuICAgIHJldHVybiB2YWx1ZSA9PT0gbGlzdGVuZXJzID8gem9vbSA6IHZhbHVlO1xuICB9O1xuXG4gIHpvb20uY2xpY2tEaXN0YW5jZSA9IGZ1bmN0aW9uKF8pIHtcbiAgICByZXR1cm4gYXJndW1lbnRzLmxlbmd0aCA/IChjbGlja0Rpc3RhbmNlMiA9IChfID0gK18pICogXywgem9vbSkgOiBNYXRoLnNxcnQoY2xpY2tEaXN0YW5jZTIpO1xuICB9O1xuXG4gIHpvb20udGFwRGlzdGFuY2UgPSBmdW5jdGlvbihfKSB7XG4gICAgcmV0dXJuIGFyZ3VtZW50cy5sZW5ndGggPyAodGFwRGlzdGFuY2UgPSArXywgem9vbSkgOiB0YXBEaXN0YW5jZTtcbiAgfTtcblxuICByZXR1cm4gem9vbTtcbn1cbiIsInZhciBoYXMgPSBPYmplY3QucHJvdG90eXBlLmhhc093blByb3BlcnR5O1xuXG5leHBvcnQgZnVuY3Rpb24gZGVxdWFsKGZvbywgYmFyKSB7XG5cdHZhciBjdG9yLCBsZW47XG5cdGlmIChmb28gPT09IGJhcikgcmV0dXJuIHRydWU7XG5cblx0aWYgKGZvbyAmJiBiYXIgJiYgKGN0b3I9Zm9vLmNvbnN0cnVjdG9yKSA9PT0gYmFyLmNvbnN0cnVjdG9yKSB7XG5cdFx0aWYgKGN0b3IgPT09IERhdGUpIHJldHVybiBmb28uZ2V0VGltZSgpID09PSBiYXIuZ2V0VGltZSgpO1xuXHRcdGlmIChjdG9yID09PSBSZWdFeHApIHJldHVybiBmb28udG9TdHJpbmcoKSA9PT0gYmFyLnRvU3RyaW5nKCk7XG5cblx0XHRpZiAoY3RvciA9PT0gQXJyYXkpIHtcblx0XHRcdGlmICgobGVuPWZvby5sZW5ndGgpID09PSBiYXIubGVuZ3RoKSB7XG5cdFx0XHRcdHdoaWxlIChsZW4tLSAmJiBkZXF1YWwoZm9vW2xlbl0sIGJhcltsZW5dKSk7XG5cdFx0XHR9XG5cdFx0XHRyZXR1cm4gbGVuID09PSAtMTtcblx0XHR9XG5cblx0XHRpZiAoIWN0b3IgfHwgdHlwZW9mIGZvbyA9PT0gJ29iamVjdCcpIHtcblx0XHRcdGxlbiA9IDA7XG5cdFx0XHRmb3IgKGN0b3IgaW4gZm9vKSB7XG5cdFx0XHRcdGlmIChoYXMuY2FsbChmb28sIGN0b3IpICYmICsrbGVuICYmICFoYXMuY2FsbChiYXIsIGN0b3IpKSByZXR1cm4gZmFsc2U7XG5cdFx0XHRcdGlmICghKGN0b3IgaW4gYmFyKSB8fCAhZGVxdWFsKGZvb1tjdG9yXSwgYmFyW2N0b3JdKSkgcmV0dXJuIGZhbHNlO1xuXHRcdFx0fVxuXHRcdFx0cmV0dXJuIE9iamVjdC5rZXlzKGJhcikubGVuZ3RoID09PSBsZW47XG5cdFx0fVxuXHR9XG5cblx0cmV0dXJuIGZvbyAhPT0gZm9vICYmIGJhciAhPT0gYmFyO1xufVxuIiwidmFyIGNsb25lID0gKGZ1bmN0aW9uKCkge1xuJ3VzZSBzdHJpY3QnO1xuXG5mdW5jdGlvbiBfaW5zdGFuY2VvZihvYmosIHR5cGUpIHtcbiAgcmV0dXJuIHR5cGUgIT0gbnVsbCAmJiBvYmogaW5zdGFuY2VvZiB0eXBlO1xufVxuXG52YXIgbmF0aXZlTWFwO1xudHJ5IHtcbiAgbmF0aXZlTWFwID0gTWFwO1xufSBjYXRjaChfKSB7XG4gIC8vIG1heWJlIGEgcmVmZXJlbmNlIGVycm9yIGJlY2F1c2Ugbm8gYE1hcGAuIEdpdmUgaXQgYSBkdW1teSB2YWx1ZSB0aGF0IG5vXG4gIC8vIHZhbHVlIHdpbGwgZXZlciBiZSBhbiBpbnN0YW5jZW9mLlxuICBuYXRpdmVNYXAgPSBmdW5jdGlvbigpIHt9O1xufVxuXG52YXIgbmF0aXZlU2V0O1xudHJ5IHtcbiAgbmF0aXZlU2V0ID0gU2V0O1xufSBjYXRjaChfKSB7XG4gIG5hdGl2ZVNldCA9IGZ1bmN0aW9uKCkge307XG59XG5cbnZhciBuYXRpdmVQcm9taXNlO1xudHJ5IHtcbiAgbmF0aXZlUHJvbWlzZSA9IFByb21pc2U7XG59IGNhdGNoKF8pIHtcbiAgbmF0aXZlUHJvbWlzZSA9IGZ1bmN0aW9uKCkge307XG59XG5cbi8qKlxuICogQ2xvbmVzIChjb3BpZXMpIGFuIE9iamVjdCB1c2luZyBkZWVwIGNvcHlpbmcuXG4gKlxuICogVGhpcyBmdW5jdGlvbiBzdXBwb3J0cyBjaXJjdWxhciByZWZlcmVuY2VzIGJ5IGRlZmF1bHQsIGJ1dCBpZiB5b3UgYXJlIGNlcnRhaW5cbiAqIHRoZXJlIGFyZSBubyBjaXJjdWxhciByZWZlcmVuY2VzIGluIHlvdXIgb2JqZWN0LCB5b3UgY2FuIHNhdmUgc29tZSBDUFUgdGltZVxuICogYnkgY2FsbGluZyBjbG9uZShvYmosIGZhbHNlKS5cbiAqXG4gKiBDYXV0aW9uOiBpZiBgY2lyY3VsYXJgIGlzIGZhbHNlIGFuZCBgcGFyZW50YCBjb250YWlucyBjaXJjdWxhciByZWZlcmVuY2VzLFxuICogeW91ciBwcm9ncmFtIG1heSBlbnRlciBhbiBpbmZpbml0ZSBsb29wIGFuZCBjcmFzaC5cbiAqXG4gKiBAcGFyYW0gYHBhcmVudGAgLSB0aGUgb2JqZWN0IHRvIGJlIGNsb25lZFxuICogQHBhcmFtIGBjaXJjdWxhcmAgLSBzZXQgdG8gdHJ1ZSBpZiB0aGUgb2JqZWN0IHRvIGJlIGNsb25lZCBtYXkgY29udGFpblxuICogICAgY2lyY3VsYXIgcmVmZXJlbmNlcy4gKG9wdGlvbmFsIC0gdHJ1ZSBieSBkZWZhdWx0KVxuICogQHBhcmFtIGBkZXB0aGAgLSBzZXQgdG8gYSBudW1iZXIgaWYgdGhlIG9iamVjdCBpcyBvbmx5IHRvIGJlIGNsb25lZCB0b1xuICogICAgYSBwYXJ0aWN1bGFyIGRlcHRoLiAob3B0aW9uYWwgLSBkZWZhdWx0cyB0byBJbmZpbml0eSlcbiAqIEBwYXJhbSBgcHJvdG90eXBlYCAtIHNldHMgdGhlIHByb3RvdHlwZSB0byBiZSB1c2VkIHdoZW4gY2xvbmluZyBhbiBvYmplY3QuXG4gKiAgICAob3B0aW9uYWwgLSBkZWZhdWx0cyB0byBwYXJlbnQgcHJvdG90eXBlKS5cbiAqIEBwYXJhbSBgaW5jbHVkZU5vbkVudW1lcmFibGVgIC0gc2V0IHRvIHRydWUgaWYgdGhlIG5vbi1lbnVtZXJhYmxlIHByb3BlcnRpZXNcbiAqICAgIHNob3VsZCBiZSBjbG9uZWQgYXMgd2VsbC4gTm9uLWVudW1lcmFibGUgcHJvcGVydGllcyBvbiB0aGUgcHJvdG90eXBlXG4gKiAgICBjaGFpbiB3aWxsIGJlIGlnbm9yZWQuIChvcHRpb25hbCAtIGZhbHNlIGJ5IGRlZmF1bHQpXG4qL1xuZnVuY3Rpb24gY2xvbmUocGFyZW50LCBjaXJjdWxhciwgZGVwdGgsIHByb3RvdHlwZSwgaW5jbHVkZU5vbkVudW1lcmFibGUpIHtcbiAgaWYgKHR5cGVvZiBjaXJjdWxhciA9PT0gJ29iamVjdCcpIHtcbiAgICBkZXB0aCA9IGNpcmN1bGFyLmRlcHRoO1xuICAgIHByb3RvdHlwZSA9IGNpcmN1bGFyLnByb3RvdHlwZTtcbiAgICBpbmNsdWRlTm9uRW51bWVyYWJsZSA9IGNpcmN1bGFyLmluY2x1ZGVOb25FbnVtZXJhYmxlO1xuICAgIGNpcmN1bGFyID0gY2lyY3VsYXIuY2lyY3VsYXI7XG4gIH1cbiAgLy8gbWFpbnRhaW4gdHdvIGFycmF5cyBmb3IgY2lyY3VsYXIgcmVmZXJlbmNlcywgd2hlcmUgY29ycmVzcG9uZGluZyBwYXJlbnRzXG4gIC8vIGFuZCBjaGlsZHJlbiBoYXZlIHRoZSBzYW1lIGluZGV4XG4gIHZhciBhbGxQYXJlbnRzID0gW107XG4gIHZhciBhbGxDaGlsZHJlbiA9IFtdO1xuXG4gIHZhciB1c2VCdWZmZXIgPSB0eXBlb2YgQnVmZmVyICE9ICd1bmRlZmluZWQnO1xuXG4gIGlmICh0eXBlb2YgY2lyY3VsYXIgPT0gJ3VuZGVmaW5lZCcpXG4gICAgY2lyY3VsYXIgPSB0cnVlO1xuXG4gIGlmICh0eXBlb2YgZGVwdGggPT0gJ3VuZGVmaW5lZCcpXG4gICAgZGVwdGggPSBJbmZpbml0eTtcblxuICAvLyByZWN1cnNlIHRoaXMgZnVuY3Rpb24gc28gd2UgZG9uJ3QgcmVzZXQgYWxsUGFyZW50cyBhbmQgYWxsQ2hpbGRyZW5cbiAgZnVuY3Rpb24gX2Nsb25lKHBhcmVudCwgZGVwdGgpIHtcbiAgICAvLyBjbG9uaW5nIG51bGwgYWx3YXlzIHJldHVybnMgbnVsbFxuICAgIGlmIChwYXJlbnQgPT09IG51bGwpXG4gICAgICByZXR1cm4gbnVsbDtcblxuICAgIGlmIChkZXB0aCA9PT0gMClcbiAgICAgIHJldHVybiBwYXJlbnQ7XG5cbiAgICB2YXIgY2hpbGQ7XG4gICAgdmFyIHByb3RvO1xuICAgIGlmICh0eXBlb2YgcGFyZW50ICE9ICdvYmplY3QnKSB7XG4gICAgICByZXR1cm4gcGFyZW50O1xuICAgIH1cblxuICAgIGlmIChfaW5zdGFuY2VvZihwYXJlbnQsIG5hdGl2ZU1hcCkpIHtcbiAgICAgIGNoaWxkID0gbmV3IG5hdGl2ZU1hcCgpO1xuICAgIH0gZWxzZSBpZiAoX2luc3RhbmNlb2YocGFyZW50LCBuYXRpdmVTZXQpKSB7XG4gICAgICBjaGlsZCA9IG5ldyBuYXRpdmVTZXQoKTtcbiAgICB9IGVsc2UgaWYgKF9pbnN0YW5jZW9mKHBhcmVudCwgbmF0aXZlUHJvbWlzZSkpIHtcbiAgICAgIGNoaWxkID0gbmV3IG5hdGl2ZVByb21pc2UoZnVuY3Rpb24gKHJlc29sdmUsIHJlamVjdCkge1xuICAgICAgICBwYXJlbnQudGhlbihmdW5jdGlvbih2YWx1ZSkge1xuICAgICAgICAgIHJlc29sdmUoX2Nsb25lKHZhbHVlLCBkZXB0aCAtIDEpKTtcbiAgICAgICAgfSwgZnVuY3Rpb24oZXJyKSB7XG4gICAgICAgICAgcmVqZWN0KF9jbG9uZShlcnIsIGRlcHRoIC0gMSkpO1xuICAgICAgICB9KTtcbiAgICAgIH0pO1xuICAgIH0gZWxzZSBpZiAoY2xvbmUuX19pc0FycmF5KHBhcmVudCkpIHtcbiAgICAgIGNoaWxkID0gW107XG4gICAgfSBlbHNlIGlmIChjbG9uZS5fX2lzUmVnRXhwKHBhcmVudCkpIHtcbiAgICAgIGNoaWxkID0gbmV3IFJlZ0V4cChwYXJlbnQuc291cmNlLCBfX2dldFJlZ0V4cEZsYWdzKHBhcmVudCkpO1xuICAgICAgaWYgKHBhcmVudC5sYXN0SW5kZXgpIGNoaWxkLmxhc3RJbmRleCA9IHBhcmVudC5sYXN0SW5kZXg7XG4gICAgfSBlbHNlIGlmIChjbG9uZS5fX2lzRGF0ZShwYXJlbnQpKSB7XG4gICAgICBjaGlsZCA9IG5ldyBEYXRlKHBhcmVudC5nZXRUaW1lKCkpO1xuICAgIH0gZWxzZSBpZiAodXNlQnVmZmVyICYmIEJ1ZmZlci5pc0J1ZmZlcihwYXJlbnQpKSB7XG4gICAgICBpZiAoQnVmZmVyLmFsbG9jVW5zYWZlKSB7XG4gICAgICAgIC8vIE5vZGUuanMgPj0gNC41LjBcbiAgICAgICAgY2hpbGQgPSBCdWZmZXIuYWxsb2NVbnNhZmUocGFyZW50Lmxlbmd0aCk7XG4gICAgICB9IGVsc2Uge1xuICAgICAgICAvLyBPbGRlciBOb2RlLmpzIHZlcnNpb25zXG4gICAgICAgIGNoaWxkID0gbmV3IEJ1ZmZlcihwYXJlbnQubGVuZ3RoKTtcbiAgICAgIH1cbiAgICAgIHBhcmVudC5jb3B5KGNoaWxkKTtcbiAgICAgIHJldHVybiBjaGlsZDtcbiAgICB9IGVsc2UgaWYgKF9pbnN0YW5jZW9mKHBhcmVudCwgRXJyb3IpKSB7XG4gICAgICBjaGlsZCA9IE9iamVjdC5jcmVhdGUocGFyZW50KTtcbiAgICB9IGVsc2Uge1xuICAgICAgaWYgKHR5cGVvZiBwcm90b3R5cGUgPT0gJ3VuZGVmaW5lZCcpIHtcbiAgICAgICAgcHJvdG8gPSBPYmplY3QuZ2V0UHJvdG90eXBlT2YocGFyZW50KTtcbiAgICAgICAgY2hpbGQgPSBPYmplY3QuY3JlYXRlKHByb3RvKTtcbiAgICAgIH1cbiAgICAgIGVsc2Uge1xuICAgICAgICBjaGlsZCA9IE9iamVjdC5jcmVhdGUocHJvdG90eXBlKTtcbiAgICAgICAgcHJvdG8gPSBwcm90b3R5cGU7XG4gICAgICB9XG4gICAgfVxuXG4gICAgaWYgKGNpcmN1bGFyKSB7XG4gICAgICB2YXIgaW5kZXggPSBhbGxQYXJlbnRzLmluZGV4T2YocGFyZW50KTtcblxuICAgICAgaWYgKGluZGV4ICE9IC0xKSB7XG4gICAgICAgIHJldHVybiBhbGxDaGlsZHJlbltpbmRleF07XG4gICAgICB9XG4gICAgICBhbGxQYXJlbnRzLnB1c2gocGFyZW50KTtcbiAgICAgIGFsbENoaWxkcmVuLnB1c2goY2hpbGQpO1xuICAgIH1cblxuICAgIGlmIChfaW5zdGFuY2VvZihwYXJlbnQsIG5hdGl2ZU1hcCkpIHtcbiAgICAgIHBhcmVudC5mb3JFYWNoKGZ1bmN0aW9uKHZhbHVlLCBrZXkpIHtcbiAgICAgICAgdmFyIGtleUNoaWxkID0gX2Nsb25lKGtleSwgZGVwdGggLSAxKTtcbiAgICAgICAgdmFyIHZhbHVlQ2hpbGQgPSBfY2xvbmUodmFsdWUsIGRlcHRoIC0gMSk7XG4gICAgICAgIGNoaWxkLnNldChrZXlDaGlsZCwgdmFsdWVDaGlsZCk7XG4gICAgICB9KTtcbiAgICB9XG4gICAgaWYgKF9pbnN0YW5jZW9mKHBhcmVudCwgbmF0aXZlU2V0KSkge1xuICAgICAgcGFyZW50LmZvckVhY2goZnVuY3Rpb24odmFsdWUpIHtcbiAgICAgICAgdmFyIGVudHJ5Q2hpbGQgPSBfY2xvbmUodmFsdWUsIGRlcHRoIC0gMSk7XG4gICAgICAgIGNoaWxkLmFkZChlbnRyeUNoaWxkKTtcbiAgICAgIH0pO1xuICAgIH1cblxuICAgIGZvciAodmFyIGkgaW4gcGFyZW50KSB7XG4gICAgICB2YXIgYXR0cnM7XG4gICAgICBpZiAocHJvdG8pIHtcbiAgICAgICAgYXR0cnMgPSBPYmplY3QuZ2V0T3duUHJvcGVydHlEZXNjcmlwdG9yKHByb3RvLCBpKTtcbiAgICAgIH1cblxuICAgICAgaWYgKGF0dHJzICYmIGF0dHJzLnNldCA9PSBudWxsKSB7XG4gICAgICAgIGNvbnRpbnVlO1xuICAgICAgfVxuICAgICAgY2hpbGRbaV0gPSBfY2xvbmUocGFyZW50W2ldLCBkZXB0aCAtIDEpO1xuICAgIH1cblxuICAgIGlmIChPYmplY3QuZ2V0T3duUHJvcGVydHlTeW1ib2xzKSB7XG4gICAgICB2YXIgc3ltYm9scyA9IE9iamVjdC5nZXRPd25Qcm9wZXJ0eVN5bWJvbHMocGFyZW50KTtcbiAgICAgIGZvciAodmFyIGkgPSAwOyBpIDwgc3ltYm9scy5sZW5ndGg7IGkrKykge1xuICAgICAgICAvLyBEb24ndCBuZWVkIHRvIHdvcnJ5IGFib3V0IGNsb25pbmcgYSBzeW1ib2wgYmVjYXVzZSBpdCBpcyBhIHByaW1pdGl2ZSxcbiAgICAgICAgLy8gbGlrZSBhIG51bWJlciBvciBzdHJpbmcuXG4gICAgICAgIHZhciBzeW1ib2wgPSBzeW1ib2xzW2ldO1xuICAgICAgICB2YXIgZGVzY3JpcHRvciA9IE9iamVjdC5nZXRPd25Qcm9wZXJ0eURlc2NyaXB0b3IocGFyZW50LCBzeW1ib2wpO1xuICAgICAgICBpZiAoZGVzY3JpcHRvciAmJiAhZGVzY3JpcHRvci5lbnVtZXJhYmxlICYmICFpbmNsdWRlTm9uRW51bWVyYWJsZSkge1xuICAgICAgICAgIGNvbnRpbnVlO1xuICAgICAgICB9XG4gICAgICAgIGNoaWxkW3N5bWJvbF0gPSBfY2xvbmUocGFyZW50W3N5bWJvbF0sIGRlcHRoIC0gMSk7XG4gICAgICAgIGlmICghZGVzY3JpcHRvci5lbnVtZXJhYmxlKSB7XG4gICAgICAgICAgT2JqZWN0LmRlZmluZVByb3BlcnR5KGNoaWxkLCBzeW1ib2wsIHtcbiAgICAgICAgICAgIGVudW1lcmFibGU6IGZhbHNlXG4gICAgICAgICAgfSk7XG4gICAgICAgIH1cbiAgICAgIH1cbiAgICB9XG5cbiAgICBpZiAoaW5jbHVkZU5vbkVudW1lcmFibGUpIHtcbiAgICAgIHZhciBhbGxQcm9wZXJ0eU5hbWVzID0gT2JqZWN0LmdldE93blByb3BlcnR5TmFtZXMocGFyZW50KTtcbiAgICAgIGZvciAodmFyIGkgPSAwOyBpIDwgYWxsUHJvcGVydHlOYW1lcy5sZW5ndGg7IGkrKykge1xuICAgICAgICB2YXIgcHJvcGVydHlOYW1lID0gYWxsUHJvcGVydHlOYW1lc1tpXTtcbiAgICAgICAgdmFyIGRlc2NyaXB0b3IgPSBPYmplY3QuZ2V0T3duUHJvcGVydHlEZXNjcmlwdG9yKHBhcmVudCwgcHJvcGVydHlOYW1lKTtcbiAgICAgICAgaWYgKGRlc2NyaXB0b3IgJiYgZGVzY3JpcHRvci5lbnVtZXJhYmxlKSB7XG4gICAgICAgICAgY29udGludWU7XG4gICAgICAgIH1cbiAgICAgICAgY2hpbGRbcHJvcGVydHlOYW1lXSA9IF9jbG9uZShwYXJlbnRbcHJvcGVydHlOYW1lXSwgZGVwdGggLSAxKTtcbiAgICAgICAgT2JqZWN0LmRlZmluZVByb3BlcnR5KGNoaWxkLCBwcm9wZXJ0eU5hbWUsIHtcbiAgICAgICAgICBlbnVtZXJhYmxlOiBmYWxzZVxuICAgICAgICB9KTtcbiAgICAgIH1cbiAgICB9XG5cbiAgICByZXR1cm4gY2hpbGQ7XG4gIH1cblxuICByZXR1cm4gX2Nsb25lKHBhcmVudCwgZGVwdGgpO1xufVxuXG4vKipcbiAqIFNpbXBsZSBmbGF0IGNsb25lIHVzaW5nIHByb3RvdHlwZSwgYWNjZXB0cyBvbmx5IG9iamVjdHMsIHVzZWZ1bGwgZm9yIHByb3BlcnR5XG4gKiBvdmVycmlkZSBvbiBGTEFUIGNvbmZpZ3VyYXRpb24gb2JqZWN0IChubyBuZXN0ZWQgcHJvcHMpLlxuICpcbiAqIFVTRSBXSVRIIENBVVRJT04hIFRoaXMgbWF5IG5vdCBiZWhhdmUgYXMgeW91IHdpc2ggaWYgeW91IGRvIG5vdCBrbm93IGhvdyB0aGlzXG4gKiB3b3Jrcy5cbiAqL1xuY2xvbmUuY2xvbmVQcm90b3R5cGUgPSBmdW5jdGlvbiBjbG9uZVByb3RvdHlwZShwYXJlbnQpIHtcbiAgaWYgKHBhcmVudCA9PT0gbnVsbClcbiAgICByZXR1cm4gbnVsbDtcblxuICB2YXIgYyA9IGZ1bmN0aW9uICgpIHt9O1xuICBjLnByb3RvdHlwZSA9IHBhcmVudDtcbiAgcmV0dXJuIG5ldyBjKCk7XG59O1xuXG4vLyBwcml2YXRlIHV0aWxpdHkgZnVuY3Rpb25zXG5cbmZ1bmN0aW9uIF9fb2JqVG9TdHIobykge1xuICByZXR1cm4gT2JqZWN0LnByb3RvdHlwZS50b1N0cmluZy5jYWxsKG8pO1xufVxuY2xvbmUuX19vYmpUb1N0ciA9IF9fb2JqVG9TdHI7XG5cbmZ1bmN0aW9uIF9faXNEYXRlKG8pIHtcbiAgcmV0dXJuIHR5cGVvZiBvID09PSAnb2JqZWN0JyAmJiBfX29ialRvU3RyKG8pID09PSAnW29iamVjdCBEYXRlXSc7XG59XG5jbG9uZS5fX2lzRGF0ZSA9IF9faXNEYXRlO1xuXG5mdW5jdGlvbiBfX2lzQXJyYXkobykge1xuICByZXR1cm4gdHlwZW9mIG8gPT09ICdvYmplY3QnICYmIF9fb2JqVG9TdHIobykgPT09ICdbb2JqZWN0IEFycmF5XSc7XG59XG5jbG9uZS5fX2lzQXJyYXkgPSBfX2lzQXJyYXk7XG5cbmZ1bmN0aW9uIF9faXNSZWdFeHAobykge1xuICByZXR1cm4gdHlwZW9mIG8gPT09ICdvYmplY3QnICYmIF9fb2JqVG9TdHIobykgPT09ICdbb2JqZWN0IFJlZ0V4cF0nO1xufVxuY2xvbmUuX19pc1JlZ0V4cCA9IF9faXNSZWdFeHA7XG5cbmZ1bmN0aW9uIF9fZ2V0UmVnRXhwRmxhZ3MocmUpIHtcbiAgdmFyIGZsYWdzID0gJyc7XG4gIGlmIChyZS5nbG9iYWwpIGZsYWdzICs9ICdnJztcbiAgaWYgKHJlLmlnbm9yZUNhc2UpIGZsYWdzICs9ICdpJztcbiAgaWYgKHJlLm11bHRpbGluZSkgZmxhZ3MgKz0gJ20nO1xuICByZXR1cm4gZmxhZ3M7XG59XG5jbG9uZS5fX2dldFJlZ0V4cEZsYWdzID0gX19nZXRSZWdFeHBGbGFncztcblxucmV0dXJuIGNsb25lO1xufSkoKTtcblxuaWYgKHR5cGVvZiBtb2R1bGUgPT09ICdvYmplY3QnICYmIG1vZHVsZS5leHBvcnRzKSB7XG4gIG1vZHVsZS5leHBvcnRzID0gY2xvbmU7XG59XG4iLCIvLyBVbmlxdWUgSUQgY3JlYXRpb24gcmVxdWlyZXMgYSBoaWdoIHF1YWxpdHkgcmFuZG9tICMgZ2VuZXJhdG9yLiBJbiB0aGUgYnJvd3NlciB3ZSB0aGVyZWZvcmVcbi8vIHJlcXVpcmUgdGhlIGNyeXB0byBBUEkgYW5kIGRvIG5vdCBzdXBwb3J0IGJ1aWx0LWluIGZhbGxiYWNrIHRvIGxvd2VyIHF1YWxpdHkgcmFuZG9tIG51bWJlclxuLy8gZ2VuZXJhdG9ycyAobGlrZSBNYXRoLnJhbmRvbSgpKS5cbnZhciBnZXRSYW5kb21WYWx1ZXM7XG52YXIgcm5kczggPSBuZXcgVWludDhBcnJheSgxNik7XG5leHBvcnQgZGVmYXVsdCBmdW5jdGlvbiBybmcoKSB7XG4gIC8vIGxhenkgbG9hZCBzbyB0aGF0IGVudmlyb25tZW50cyB0aGF0IG5lZWQgdG8gcG9seWZpbGwgaGF2ZSBhIGNoYW5jZSB0byBkbyBzb1xuICBpZiAoIWdldFJhbmRvbVZhbHVlcykge1xuICAgIC8vIGdldFJhbmRvbVZhbHVlcyBuZWVkcyB0byBiZSBpbnZva2VkIGluIGEgY29udGV4dCB3aGVyZSBcInRoaXNcIiBpcyBhIENyeXB0byBpbXBsZW1lbnRhdGlvbi4gQWxzbyxcbiAgICAvLyBmaW5kIHRoZSBjb21wbGV0ZSBpbXBsZW1lbnRhdGlvbiBvZiBjcnlwdG8gKG1zQ3J5cHRvKSBvbiBJRTExLlxuICAgIGdldFJhbmRvbVZhbHVlcyA9IHR5cGVvZiBjcnlwdG8gIT09ICd1bmRlZmluZWQnICYmIGNyeXB0by5nZXRSYW5kb21WYWx1ZXMgJiYgY3J5cHRvLmdldFJhbmRvbVZhbHVlcy5iaW5kKGNyeXB0bykgfHwgdHlwZW9mIG1zQ3J5cHRvICE9PSAndW5kZWZpbmVkJyAmJiB0eXBlb2YgbXNDcnlwdG8uZ2V0UmFuZG9tVmFsdWVzID09PSAnZnVuY3Rpb24nICYmIG1zQ3J5cHRvLmdldFJhbmRvbVZhbHVlcy5iaW5kKG1zQ3J5cHRvKTtcblxuICAgIGlmICghZ2V0UmFuZG9tVmFsdWVzKSB7XG4gICAgICB0aHJvdyBuZXcgRXJyb3IoJ2NyeXB0by5nZXRSYW5kb21WYWx1ZXMoKSBub3Qgc3VwcG9ydGVkLiBTZWUgaHR0cHM6Ly9naXRodWIuY29tL3V1aWRqcy91dWlkI2dldHJhbmRvbXZhbHVlcy1ub3Qtc3VwcG9ydGVkJyk7XG4gICAgfVxuICB9XG5cbiAgcmV0dXJuIGdldFJhbmRvbVZhbHVlcyhybmRzOCk7XG59IiwiZXhwb3J0IGRlZmF1bHQgL14oPzpbMC05YS1mXXs4fS1bMC05YS1mXXs0fS1bMS01XVswLTlhLWZdezN9LVs4OWFiXVswLTlhLWZdezN9LVswLTlhLWZdezEyfXwwMDAwMDAwMC0wMDAwLTAwMDAtMDAwMC0wMDAwMDAwMDAwMDApJC9pOyIsImltcG9ydCBSRUdFWCBmcm9tICcuL3JlZ2V4LmpzJztcblxuZnVuY3Rpb24gdmFsaWRhdGUodXVpZCkge1xuICByZXR1cm4gdHlwZW9mIHV1aWQgPT09ICdzdHJpbmcnICYmIFJFR0VYLnRlc3QodXVpZCk7XG59XG5cbmV4cG9ydCBkZWZhdWx0IHZhbGlkYXRlOyIsImltcG9ydCB2YWxpZGF0ZSBmcm9tICcuL3ZhbGlkYXRlLmpzJztcbi8qKlxuICogQ29udmVydCBhcnJheSBvZiAxNiBieXRlIHZhbHVlcyB0byBVVUlEIHN0cmluZyBmb3JtYXQgb2YgdGhlIGZvcm06XG4gKiBYWFhYWFhYWC1YWFhYLVhYWFgtWFhYWC1YWFhYWFhYWFhYWFhcbiAqL1xuXG52YXIgYnl0ZVRvSGV4ID0gW107XG5cbmZvciAodmFyIGkgPSAwOyBpIDwgMjU2OyArK2kpIHtcbiAgYnl0ZVRvSGV4LnB1c2goKGkgKyAweDEwMCkudG9TdHJpbmcoMTYpLnN1YnN0cigxKSk7XG59XG5cbmZ1bmN0aW9uIHN0cmluZ2lmeShhcnIpIHtcbiAgdmFyIG9mZnNldCA9IGFyZ3VtZW50cy5sZW5ndGggPiAxICYmIGFyZ3VtZW50c1sxXSAhPT0gdW5kZWZpbmVkID8gYXJndW1lbnRzWzFdIDogMDtcbiAgLy8gTm90ZTogQmUgY2FyZWZ1bCBlZGl0aW5nIHRoaXMgY29kZSEgIEl0J3MgYmVlbiB0dW5lZCBmb3IgcGVyZm9ybWFuY2VcbiAgLy8gYW5kIHdvcmtzIGluIHdheXMgeW91IG1heSBub3QgZXhwZWN0LiBTZWUgaHR0cHM6Ly9naXRodWIuY29tL3V1aWRqcy91dWlkL3B1bGwvNDM0XG4gIHZhciB1dWlkID0gKGJ5dGVUb0hleFthcnJbb2Zmc2V0ICsgMF1dICsgYnl0ZVRvSGV4W2FycltvZmZzZXQgKyAxXV0gKyBieXRlVG9IZXhbYXJyW29mZnNldCArIDJdXSArIGJ5dGVUb0hleFthcnJbb2Zmc2V0ICsgM11dICsgJy0nICsgYnl0ZVRvSGV4W2FycltvZmZzZXQgKyA0XV0gKyBieXRlVG9IZXhbYXJyW29mZnNldCArIDVdXSArICctJyArIGJ5dGVUb0hleFthcnJbb2Zmc2V0ICsgNl1dICsgYnl0ZVRvSGV4W2FycltvZmZzZXQgKyA3XV0gKyAnLScgKyBieXRlVG9IZXhbYXJyW29mZnNldCArIDhdXSArIGJ5dGVUb0hleFthcnJbb2Zmc2V0ICsgOV1dICsgJy0nICsgYnl0ZVRvSGV4W2FycltvZmZzZXQgKyAxMF1dICsgYnl0ZVRvSGV4W2FycltvZmZzZXQgKyAxMV1dICsgYnl0ZVRvSGV4W2FycltvZmZzZXQgKyAxMl1dICsgYnl0ZVRvSGV4W2FycltvZmZzZXQgKyAxM11dICsgYnl0ZVRvSGV4W2FycltvZmZzZXQgKyAxNF1dICsgYnl0ZVRvSGV4W2FycltvZmZzZXQgKyAxNV1dKS50b0xvd2VyQ2FzZSgpOyAvLyBDb25zaXN0ZW5jeSBjaGVjayBmb3IgdmFsaWQgVVVJRC4gIElmIHRoaXMgdGhyb3dzLCBpdCdzIGxpa2VseSBkdWUgdG8gb25lXG4gIC8vIG9mIHRoZSBmb2xsb3dpbmc6XG4gIC8vIC0gT25lIG9yIG1vcmUgaW5wdXQgYXJyYXkgdmFsdWVzIGRvbid0IG1hcCB0byBhIGhleCBvY3RldCAobGVhZGluZyB0b1xuICAvLyBcInVuZGVmaW5lZFwiIGluIHRoZSB1dWlkKVxuICAvLyAtIEludmFsaWQgaW5wdXQgdmFsdWVzIGZvciB0aGUgUkZDIGB2ZXJzaW9uYCBvciBgdmFyaWFudGAgZmllbGRzXG5cbiAgaWYgKCF2YWxpZGF0ZSh1dWlkKSkge1xuICAgIHRocm93IFR5cGVFcnJvcignU3RyaW5naWZpZWQgVVVJRCBpcyBpbnZhbGlkJyk7XG4gIH1cblxuICByZXR1cm4gdXVpZDtcbn1cblxuZXhwb3J0IGRlZmF1bHQgc3RyaW5naWZ5OyIsImltcG9ydCBybmcgZnJvbSAnLi9ybmcuanMnO1xuaW1wb3J0IHN0cmluZ2lmeSBmcm9tICcuL3N0cmluZ2lmeS5qcyc7XG5cbmZ1bmN0aW9uIHY0KG9wdGlvbnMsIGJ1Ziwgb2Zmc2V0KSB7XG4gIG9wdGlvbnMgPSBvcHRpb25zIHx8IHt9O1xuICB2YXIgcm5kcyA9IG9wdGlvbnMucmFuZG9tIHx8IChvcHRpb25zLnJuZyB8fCBybmcpKCk7IC8vIFBlciA0LjQsIHNldCBiaXRzIGZvciB2ZXJzaW9uIGFuZCBgY2xvY2tfc2VxX2hpX2FuZF9yZXNlcnZlZGBcblxuICBybmRzWzZdID0gcm5kc1s2XSAmIDB4MGYgfCAweDQwO1xuICBybmRzWzhdID0gcm5kc1s4XSAmIDB4M2YgfCAweDgwOyAvLyBDb3B5IGJ5dGVzIHRvIGJ1ZmZlciwgaWYgcHJvdmlkZWRcblxuICBpZiAoYnVmKSB7XG4gICAgb2Zmc2V0ID0gb2Zmc2V0IHx8IDA7XG5cbiAgICBmb3IgKHZhciBpID0gMDsgaSA8IDE2OyArK2kpIHtcbiAgICAgIGJ1ZltvZmZzZXQgKyBpXSA9IHJuZHNbaV07XG4gICAgfVxuXG4gICAgcmV0dXJuIGJ1ZjtcbiAgfVxuXG4gIHJldHVybiBzdHJpbmdpZnkocm5kcyk7XG59XG5cbmV4cG9ydCBkZWZhdWx0IHY0OyIsIi8qKiBAbGljZW5zZSBSZWFjdCB2MTYuMTMuMVxuICogcmVhY3QtaXMuZGV2ZWxvcG1lbnQuanNcbiAqXG4gKiBDb3B5cmlnaHQgKGMpIEZhY2Vib29rLCBJbmMuIGFuZCBpdHMgYWZmaWxpYXRlcy5cbiAqXG4gKiBUaGlzIHNvdXJjZSBjb2RlIGlzIGxpY2Vuc2VkIHVuZGVyIHRoZSBNSVQgbGljZW5zZSBmb3VuZCBpbiB0aGVcbiAqIExJQ0VOU0UgZmlsZSBpbiB0aGUgcm9vdCBkaXJlY3Rvcnkgb2YgdGhpcyBzb3VyY2UgdHJlZS5cbiAqL1xuXG4ndXNlIHN0cmljdCc7XG5cblxuXG5pZiAocHJvY2Vzcy5lbnYuTk9ERV9FTlYgIT09IFwicHJvZHVjdGlvblwiKSB7XG4gIChmdW5jdGlvbigpIHtcbid1c2Ugc3RyaWN0JztcblxuLy8gVGhlIFN5bWJvbCB1c2VkIHRvIHRhZyB0aGUgUmVhY3RFbGVtZW50LWxpa2UgdHlwZXMuIElmIHRoZXJlIGlzIG5vIG5hdGl2ZSBTeW1ib2xcbi8vIG5vciBwb2x5ZmlsbCwgdGhlbiBhIHBsYWluIG51bWJlciBpcyB1c2VkIGZvciBwZXJmb3JtYW5jZS5cbnZhciBoYXNTeW1ib2wgPSB0eXBlb2YgU3ltYm9sID09PSAnZnVuY3Rpb24nICYmIFN5bWJvbC5mb3I7XG52YXIgUkVBQ1RfRUxFTUVOVF9UWVBFID0gaGFzU3ltYm9sID8gU3ltYm9sLmZvcigncmVhY3QuZWxlbWVudCcpIDogMHhlYWM3O1xudmFyIFJFQUNUX1BPUlRBTF9UWVBFID0gaGFzU3ltYm9sID8gU3ltYm9sLmZvcigncmVhY3QucG9ydGFsJykgOiAweGVhY2E7XG52YXIgUkVBQ1RfRlJBR01FTlRfVFlQRSA9IGhhc1N5bWJvbCA/IFN5bWJvbC5mb3IoJ3JlYWN0LmZyYWdtZW50JykgOiAweGVhY2I7XG52YXIgUkVBQ1RfU1RSSUNUX01PREVfVFlQRSA9IGhhc1N5bWJvbCA/IFN5bWJvbC5mb3IoJ3JlYWN0LnN0cmljdF9tb2RlJykgOiAweGVhY2M7XG52YXIgUkVBQ1RfUFJPRklMRVJfVFlQRSA9IGhhc1N5bWJvbCA/IFN5bWJvbC5mb3IoJ3JlYWN0LnByb2ZpbGVyJykgOiAweGVhZDI7XG52YXIgUkVBQ1RfUFJPVklERVJfVFlQRSA9IGhhc1N5bWJvbCA/IFN5bWJvbC5mb3IoJ3JlYWN0LnByb3ZpZGVyJykgOiAweGVhY2Q7XG52YXIgUkVBQ1RfQ09OVEVYVF9UWVBFID0gaGFzU3ltYm9sID8gU3ltYm9sLmZvcigncmVhY3QuY29udGV4dCcpIDogMHhlYWNlOyAvLyBUT0RPOiBXZSBkb24ndCB1c2UgQXN5bmNNb2RlIG9yIENvbmN1cnJlbnRNb2RlIGFueW1vcmUuIFRoZXkgd2VyZSB0ZW1wb3Jhcnlcbi8vICh1bnN0YWJsZSkgQVBJcyB0aGF0IGhhdmUgYmVlbiByZW1vdmVkLiBDYW4gd2UgcmVtb3ZlIHRoZSBzeW1ib2xzP1xuXG52YXIgUkVBQ1RfQVNZTkNfTU9ERV9UWVBFID0gaGFzU3ltYm9sID8gU3ltYm9sLmZvcigncmVhY3QuYXN5bmNfbW9kZScpIDogMHhlYWNmO1xudmFyIFJFQUNUX0NPTkNVUlJFTlRfTU9ERV9UWVBFID0gaGFzU3ltYm9sID8gU3ltYm9sLmZvcigncmVhY3QuY29uY3VycmVudF9tb2RlJykgOiAweGVhY2Y7XG52YXIgUkVBQ1RfRk9SV0FSRF9SRUZfVFlQRSA9IGhhc1N5bWJvbCA/IFN5bWJvbC5mb3IoJ3JlYWN0LmZvcndhcmRfcmVmJykgOiAweGVhZDA7XG52YXIgUkVBQ1RfU1VTUEVOU0VfVFlQRSA9IGhhc1N5bWJvbCA/IFN5bWJvbC5mb3IoJ3JlYWN0LnN1c3BlbnNlJykgOiAweGVhZDE7XG52YXIgUkVBQ1RfU1VTUEVOU0VfTElTVF9UWVBFID0gaGFzU3ltYm9sID8gU3ltYm9sLmZvcigncmVhY3Quc3VzcGVuc2VfbGlzdCcpIDogMHhlYWQ4O1xudmFyIFJFQUNUX01FTU9fVFlQRSA9IGhhc1N5bWJvbCA/IFN5bWJvbC5mb3IoJ3JlYWN0Lm1lbW8nKSA6IDB4ZWFkMztcbnZhciBSRUFDVF9MQVpZX1RZUEUgPSBoYXNTeW1ib2wgPyBTeW1ib2wuZm9yKCdyZWFjdC5sYXp5JykgOiAweGVhZDQ7XG52YXIgUkVBQ1RfQkxPQ0tfVFlQRSA9IGhhc1N5bWJvbCA/IFN5bWJvbC5mb3IoJ3JlYWN0LmJsb2NrJykgOiAweGVhZDk7XG52YXIgUkVBQ1RfRlVOREFNRU5UQUxfVFlQRSA9IGhhc1N5bWJvbCA/IFN5bWJvbC5mb3IoJ3JlYWN0LmZ1bmRhbWVudGFsJykgOiAweGVhZDU7XG52YXIgUkVBQ1RfUkVTUE9OREVSX1RZUEUgPSBoYXNTeW1ib2wgPyBTeW1ib2wuZm9yKCdyZWFjdC5yZXNwb25kZXInKSA6IDB4ZWFkNjtcbnZhciBSRUFDVF9TQ09QRV9UWVBFID0gaGFzU3ltYm9sID8gU3ltYm9sLmZvcigncmVhY3Quc2NvcGUnKSA6IDB4ZWFkNztcblxuZnVuY3Rpb24gaXNWYWxpZEVsZW1lbnRUeXBlKHR5cGUpIHtcbiAgcmV0dXJuIHR5cGVvZiB0eXBlID09PSAnc3RyaW5nJyB8fCB0eXBlb2YgdHlwZSA9PT0gJ2Z1bmN0aW9uJyB8fCAvLyBOb3RlOiBpdHMgdHlwZW9mIG1pZ2h0IGJlIG90aGVyIHRoYW4gJ3N5bWJvbCcgb3IgJ251bWJlcicgaWYgaXQncyBhIHBvbHlmaWxsLlxuICB0eXBlID09PSBSRUFDVF9GUkFHTUVOVF9UWVBFIHx8IHR5cGUgPT09IFJFQUNUX0NPTkNVUlJFTlRfTU9ERV9UWVBFIHx8IHR5cGUgPT09IFJFQUNUX1BST0ZJTEVSX1RZUEUgfHwgdHlwZSA9PT0gUkVBQ1RfU1RSSUNUX01PREVfVFlQRSB8fCB0eXBlID09PSBSRUFDVF9TVVNQRU5TRV9UWVBFIHx8IHR5cGUgPT09IFJFQUNUX1NVU1BFTlNFX0xJU1RfVFlQRSB8fCB0eXBlb2YgdHlwZSA9PT0gJ29iamVjdCcgJiYgdHlwZSAhPT0gbnVsbCAmJiAodHlwZS4kJHR5cGVvZiA9PT0gUkVBQ1RfTEFaWV9UWVBFIHx8IHR5cGUuJCR0eXBlb2YgPT09IFJFQUNUX01FTU9fVFlQRSB8fCB0eXBlLiQkdHlwZW9mID09PSBSRUFDVF9QUk9WSURFUl9UWVBFIHx8IHR5cGUuJCR0eXBlb2YgPT09IFJFQUNUX0NPTlRFWFRfVFlQRSB8fCB0eXBlLiQkdHlwZW9mID09PSBSRUFDVF9GT1JXQVJEX1JFRl9UWVBFIHx8IHR5cGUuJCR0eXBlb2YgPT09IFJFQUNUX0ZVTkRBTUVOVEFMX1RZUEUgfHwgdHlwZS4kJHR5cGVvZiA9PT0gUkVBQ1RfUkVTUE9OREVSX1RZUEUgfHwgdHlwZS4kJHR5cGVvZiA9PT0gUkVBQ1RfU0NPUEVfVFlQRSB8fCB0eXBlLiQkdHlwZW9mID09PSBSRUFDVF9CTE9DS19UWVBFKTtcbn1cblxuZnVuY3Rpb24gdHlwZU9mKG9iamVjdCkge1xuICBpZiAodHlwZW9mIG9iamVjdCA9PT0gJ29iamVjdCcgJiYgb2JqZWN0ICE9PSBudWxsKSB7XG4gICAgdmFyICQkdHlwZW9mID0gb2JqZWN0LiQkdHlwZW9mO1xuXG4gICAgc3dpdGNoICgkJHR5cGVvZikge1xuICAgICAgY2FzZSBSRUFDVF9FTEVNRU5UX1RZUEU6XG4gICAgICAgIHZhciB0eXBlID0gb2JqZWN0LnR5cGU7XG5cbiAgICAgICAgc3dpdGNoICh0eXBlKSB7XG4gICAgICAgICAgY2FzZSBSRUFDVF9BU1lOQ19NT0RFX1RZUEU6XG4gICAgICAgICAgY2FzZSBSRUFDVF9DT05DVVJSRU5UX01PREVfVFlQRTpcbiAgICAgICAgICBjYXNlIFJFQUNUX0ZSQUdNRU5UX1RZUEU6XG4gICAgICAgICAgY2FzZSBSRUFDVF9QUk9GSUxFUl9UWVBFOlxuICAgICAgICAgIGNhc2UgUkVBQ1RfU1RSSUNUX01PREVfVFlQRTpcbiAgICAgICAgICBjYXNlIFJFQUNUX1NVU1BFTlNFX1RZUEU6XG4gICAgICAgICAgICByZXR1cm4gdHlwZTtcblxuICAgICAgICAgIGRlZmF1bHQ6XG4gICAgICAgICAgICB2YXIgJCR0eXBlb2ZUeXBlID0gdHlwZSAmJiB0eXBlLiQkdHlwZW9mO1xuXG4gICAgICAgICAgICBzd2l0Y2ggKCQkdHlwZW9mVHlwZSkge1xuICAgICAgICAgICAgICBjYXNlIFJFQUNUX0NPTlRFWFRfVFlQRTpcbiAgICAgICAgICAgICAgY2FzZSBSRUFDVF9GT1JXQVJEX1JFRl9UWVBFOlxuICAgICAgICAgICAgICBjYXNlIFJFQUNUX0xBWllfVFlQRTpcbiAgICAgICAgICAgICAgY2FzZSBSRUFDVF9NRU1PX1RZUEU6XG4gICAgICAgICAgICAgIGNhc2UgUkVBQ1RfUFJPVklERVJfVFlQRTpcbiAgICAgICAgICAgICAgICByZXR1cm4gJCR0eXBlb2ZUeXBlO1xuXG4gICAgICAgICAgICAgIGRlZmF1bHQ6XG4gICAgICAgICAgICAgICAgcmV0dXJuICQkdHlwZW9mO1xuICAgICAgICAgICAgfVxuXG4gICAgICAgIH1cblxuICAgICAgY2FzZSBSRUFDVF9QT1JUQUxfVFlQRTpcbiAgICAgICAgcmV0dXJuICQkdHlwZW9mO1xuICAgIH1cbiAgfVxuXG4gIHJldHVybiB1bmRlZmluZWQ7XG59IC8vIEFzeW5jTW9kZSBpcyBkZXByZWNhdGVkIGFsb25nIHdpdGggaXNBc3luY01vZGVcblxudmFyIEFzeW5jTW9kZSA9IFJFQUNUX0FTWU5DX01PREVfVFlQRTtcbnZhciBDb25jdXJyZW50TW9kZSA9IFJFQUNUX0NPTkNVUlJFTlRfTU9ERV9UWVBFO1xudmFyIENvbnRleHRDb25zdW1lciA9IFJFQUNUX0NPTlRFWFRfVFlQRTtcbnZhciBDb250ZXh0UHJvdmlkZXIgPSBSRUFDVF9QUk9WSURFUl9UWVBFO1xudmFyIEVsZW1lbnQgPSBSRUFDVF9FTEVNRU5UX1RZUEU7XG52YXIgRm9yd2FyZFJlZiA9IFJFQUNUX0ZPUldBUkRfUkVGX1RZUEU7XG52YXIgRnJhZ21lbnQgPSBSRUFDVF9GUkFHTUVOVF9UWVBFO1xudmFyIExhenkgPSBSRUFDVF9MQVpZX1RZUEU7XG52YXIgTWVtbyA9IFJFQUNUX01FTU9fVFlQRTtcbnZhciBQb3J0YWwgPSBSRUFDVF9QT1JUQUxfVFlQRTtcbnZhciBQcm9maWxlciA9IFJFQUNUX1BST0ZJTEVSX1RZUEU7XG52YXIgU3RyaWN0TW9kZSA9IFJFQUNUX1NUUklDVF9NT0RFX1RZUEU7XG52YXIgU3VzcGVuc2UgPSBSRUFDVF9TVVNQRU5TRV9UWVBFO1xudmFyIGhhc1dhcm5lZEFib3V0RGVwcmVjYXRlZElzQXN5bmNNb2RlID0gZmFsc2U7IC8vIEFzeW5jTW9kZSBzaG91bGQgYmUgZGVwcmVjYXRlZFxuXG5mdW5jdGlvbiBpc0FzeW5jTW9kZShvYmplY3QpIHtcbiAge1xuICAgIGlmICghaGFzV2FybmVkQWJvdXREZXByZWNhdGVkSXNBc3luY01vZGUpIHtcbiAgICAgIGhhc1dhcm5lZEFib3V0RGVwcmVjYXRlZElzQXN5bmNNb2RlID0gdHJ1ZTsgLy8gVXNpbmcgY29uc29sZVsnd2FybiddIHRvIGV2YWRlIEJhYmVsIGFuZCBFU0xpbnRcblxuICAgICAgY29uc29sZVsnd2FybiddKCdUaGUgUmVhY3RJcy5pc0FzeW5jTW9kZSgpIGFsaWFzIGhhcyBiZWVuIGRlcHJlY2F0ZWQsICcgKyAnYW5kIHdpbGwgYmUgcmVtb3ZlZCBpbiBSZWFjdCAxNysuIFVwZGF0ZSB5b3VyIGNvZGUgdG8gdXNlICcgKyAnUmVhY3RJcy5pc0NvbmN1cnJlbnRNb2RlKCkgaW5zdGVhZC4gSXQgaGFzIHRoZSBleGFjdCBzYW1lIEFQSS4nKTtcbiAgICB9XG4gIH1cblxuICByZXR1cm4gaXNDb25jdXJyZW50TW9kZShvYmplY3QpIHx8IHR5cGVPZihvYmplY3QpID09PSBSRUFDVF9BU1lOQ19NT0RFX1RZUEU7XG59XG5mdW5jdGlvbiBpc0NvbmN1cnJlbnRNb2RlKG9iamVjdCkge1xuICByZXR1cm4gdHlwZU9mKG9iamVjdCkgPT09IFJFQUNUX0NPTkNVUlJFTlRfTU9ERV9UWVBFO1xufVxuZnVuY3Rpb24gaXNDb250ZXh0Q29uc3VtZXIob2JqZWN0KSB7XG4gIHJldHVybiB0eXBlT2Yob2JqZWN0KSA9PT0gUkVBQ1RfQ09OVEVYVF9UWVBFO1xufVxuZnVuY3Rpb24gaXNDb250ZXh0UHJvdmlkZXIob2JqZWN0KSB7XG4gIHJldHVybiB0eXBlT2Yob2JqZWN0KSA9PT0gUkVBQ1RfUFJPVklERVJfVFlQRTtcbn1cbmZ1bmN0aW9uIGlzRWxlbWVudChvYmplY3QpIHtcbiAgcmV0dXJuIHR5cGVvZiBvYmplY3QgPT09ICdvYmplY3QnICYmIG9iamVjdCAhPT0gbnVsbCAmJiBvYmplY3QuJCR0eXBlb2YgPT09IFJFQUNUX0VMRU1FTlRfVFlQRTtcbn1cbmZ1bmN0aW9uIGlzRm9yd2FyZFJlZihvYmplY3QpIHtcbiAgcmV0dXJuIHR5cGVPZihvYmplY3QpID09PSBSRUFDVF9GT1JXQVJEX1JFRl9UWVBFO1xufVxuZnVuY3Rpb24gaXNGcmFnbWVudChvYmplY3QpIHtcbiAgcmV0dXJuIHR5cGVPZihvYmplY3QpID09PSBSRUFDVF9GUkFHTUVOVF9UWVBFO1xufVxuZnVuY3Rpb24gaXNMYXp5KG9iamVjdCkge1xuICByZXR1cm4gdHlwZU9mKG9iamVjdCkgPT09IFJFQUNUX0xBWllfVFlQRTtcbn1cbmZ1bmN0aW9uIGlzTWVtbyhvYmplY3QpIHtcbiAgcmV0dXJuIHR5cGVPZihvYmplY3QpID09PSBSRUFDVF9NRU1PX1RZUEU7XG59XG5mdW5jdGlvbiBpc1BvcnRhbChvYmplY3QpIHtcbiAgcmV0dXJuIHR5cGVPZihvYmplY3QpID09PSBSRUFDVF9QT1JUQUxfVFlQRTtcbn1cbmZ1bmN0aW9uIGlzUHJvZmlsZXIob2JqZWN0KSB7XG4gIHJldHVybiB0eXBlT2Yob2JqZWN0KSA9PT0gUkVBQ1RfUFJPRklMRVJfVFlQRTtcbn1cbmZ1bmN0aW9uIGlzU3RyaWN0TW9kZShvYmplY3QpIHtcbiAgcmV0dXJuIHR5cGVPZihvYmplY3QpID09PSBSRUFDVF9TVFJJQ1RfTU9ERV9UWVBFO1xufVxuZnVuY3Rpb24gaXNTdXNwZW5zZShvYmplY3QpIHtcbiAgcmV0dXJuIHR5cGVPZihvYmplY3QpID09PSBSRUFDVF9TVVNQRU5TRV9UWVBFO1xufVxuXG5leHBvcnRzLkFzeW5jTW9kZSA9IEFzeW5jTW9kZTtcbmV4cG9ydHMuQ29uY3VycmVudE1vZGUgPSBDb25jdXJyZW50TW9kZTtcbmV4cG9ydHMuQ29udGV4dENvbnN1bWVyID0gQ29udGV4dENvbnN1bWVyO1xuZXhwb3J0cy5Db250ZXh0UHJvdmlkZXIgPSBDb250ZXh0UHJvdmlkZXI7XG5leHBvcnRzLkVsZW1lbnQgPSBFbGVtZW50O1xuZXhwb3J0cy5Gb3J3YXJkUmVmID0gRm9yd2FyZFJlZjtcbmV4cG9ydHMuRnJhZ21lbnQgPSBGcmFnbWVudDtcbmV4cG9ydHMuTGF6eSA9IExhenk7XG5leHBvcnRzLk1lbW8gPSBNZW1vO1xuZXhwb3J0cy5Qb3J0YWwgPSBQb3J0YWw7XG5leHBvcnRzLlByb2ZpbGVyID0gUHJvZmlsZXI7XG5leHBvcnRzLlN0cmljdE1vZGUgPSBTdHJpY3RNb2RlO1xuZXhwb3J0cy5TdXNwZW5zZSA9IFN1c3BlbnNlO1xuZXhwb3J0cy5pc0FzeW5jTW9kZSA9IGlzQXN5bmNNb2RlO1xuZXhwb3J0cy5pc0NvbmN1cnJlbnRNb2RlID0gaXNDb25jdXJyZW50TW9kZTtcbmV4cG9ydHMuaXNDb250ZXh0Q29uc3VtZXIgPSBpc0NvbnRleHRDb25zdW1lcjtcbmV4cG9ydHMuaXNDb250ZXh0UHJvdmlkZXIgPSBpc0NvbnRleHRQcm92aWRlcjtcbmV4cG9ydHMuaXNFbGVtZW50ID0gaXNFbGVtZW50O1xuZXhwb3J0cy5pc0ZvcndhcmRSZWYgPSBpc0ZvcndhcmRSZWY7XG5leHBvcnRzLmlzRnJhZ21lbnQgPSBpc0ZyYWdtZW50O1xuZXhwb3J0cy5pc0xhenkgPSBpc0xhenk7XG5leHBvcnRzLmlzTWVtbyA9IGlzTWVtbztcbmV4cG9ydHMuaXNQb3J0YWwgPSBpc1BvcnRhbDtcbmV4cG9ydHMuaXNQcm9maWxlciA9IGlzUHJvZmlsZXI7XG5leHBvcnRzLmlzU3RyaWN0TW9kZSA9IGlzU3RyaWN0TW9kZTtcbmV4cG9ydHMuaXNTdXNwZW5zZSA9IGlzU3VzcGVuc2U7XG5leHBvcnRzLmlzVmFsaWRFbGVtZW50VHlwZSA9IGlzVmFsaWRFbGVtZW50VHlwZTtcbmV4cG9ydHMudHlwZU9mID0gdHlwZU9mO1xuICB9KSgpO1xufVxuIiwiJ3VzZSBzdHJpY3QnO1xuXG5pZiAocHJvY2Vzcy5lbnYuTk9ERV9FTlYgPT09ICdwcm9kdWN0aW9uJykge1xuICBtb2R1bGUuZXhwb3J0cyA9IHJlcXVpcmUoJy4vY2pzL3JlYWN0LWlzLnByb2R1Y3Rpb24ubWluLmpzJyk7XG59IGVsc2Uge1xuICBtb2R1bGUuZXhwb3J0cyA9IHJlcXVpcmUoJy4vY2pzL3JlYWN0LWlzLmRldmVsb3BtZW50LmpzJyk7XG59XG4iLCIvKlxub2JqZWN0LWFzc2lnblxuKGMpIFNpbmRyZSBTb3JodXNcbkBsaWNlbnNlIE1JVFxuKi9cblxuJ3VzZSBzdHJpY3QnO1xuLyogZXNsaW50LWRpc2FibGUgbm8tdW51c2VkLXZhcnMgKi9cbnZhciBnZXRPd25Qcm9wZXJ0eVN5bWJvbHMgPSBPYmplY3QuZ2V0T3duUHJvcGVydHlTeW1ib2xzO1xudmFyIGhhc093blByb3BlcnR5ID0gT2JqZWN0LnByb3RvdHlwZS5oYXNPd25Qcm9wZXJ0eTtcbnZhciBwcm9wSXNFbnVtZXJhYmxlID0gT2JqZWN0LnByb3RvdHlwZS5wcm9wZXJ0eUlzRW51bWVyYWJsZTtcblxuZnVuY3Rpb24gdG9PYmplY3QodmFsKSB7XG5cdGlmICh2YWwgPT09IG51bGwgfHwgdmFsID09PSB1bmRlZmluZWQpIHtcblx0XHR0aHJvdyBuZXcgVHlwZUVycm9yKCdPYmplY3QuYXNzaWduIGNhbm5vdCBiZSBjYWxsZWQgd2l0aCBudWxsIG9yIHVuZGVmaW5lZCcpO1xuXHR9XG5cblx0cmV0dXJuIE9iamVjdCh2YWwpO1xufVxuXG5mdW5jdGlvbiBzaG91bGRVc2VOYXRpdmUoKSB7XG5cdHRyeSB7XG5cdFx0aWYgKCFPYmplY3QuYXNzaWduKSB7XG5cdFx0XHRyZXR1cm4gZmFsc2U7XG5cdFx0fVxuXG5cdFx0Ly8gRGV0ZWN0IGJ1Z2d5IHByb3BlcnR5IGVudW1lcmF0aW9uIG9yZGVyIGluIG9sZGVyIFY4IHZlcnNpb25zLlxuXG5cdFx0Ly8gaHR0cHM6Ly9idWdzLmNocm9taXVtLm9yZy9wL3Y4L2lzc3Vlcy9kZXRhaWw/aWQ9NDExOFxuXHRcdHZhciB0ZXN0MSA9IG5ldyBTdHJpbmcoJ2FiYycpOyAgLy8gZXNsaW50LWRpc2FibGUtbGluZSBuby1uZXctd3JhcHBlcnNcblx0XHR0ZXN0MVs1XSA9ICdkZSc7XG5cdFx0aWYgKE9iamVjdC5nZXRPd25Qcm9wZXJ0eU5hbWVzKHRlc3QxKVswXSA9PT0gJzUnKSB7XG5cdFx0XHRyZXR1cm4gZmFsc2U7XG5cdFx0fVxuXG5cdFx0Ly8gaHR0cHM6Ly9idWdzLmNocm9taXVtLm9yZy9wL3Y4L2lzc3Vlcy9kZXRhaWw/aWQ9MzA1NlxuXHRcdHZhciB0ZXN0MiA9IHt9O1xuXHRcdGZvciAodmFyIGkgPSAwOyBpIDwgMTA7IGkrKykge1xuXHRcdFx0dGVzdDJbJ18nICsgU3RyaW5nLmZyb21DaGFyQ29kZShpKV0gPSBpO1xuXHRcdH1cblx0XHR2YXIgb3JkZXIyID0gT2JqZWN0LmdldE93blByb3BlcnR5TmFtZXModGVzdDIpLm1hcChmdW5jdGlvbiAobikge1xuXHRcdFx0cmV0dXJuIHRlc3QyW25dO1xuXHRcdH0pO1xuXHRcdGlmIChvcmRlcjIuam9pbignJykgIT09ICcwMTIzNDU2Nzg5Jykge1xuXHRcdFx0cmV0dXJuIGZhbHNlO1xuXHRcdH1cblxuXHRcdC8vIGh0dHBzOi8vYnVncy5jaHJvbWl1bS5vcmcvcC92OC9pc3N1ZXMvZGV0YWlsP2lkPTMwNTZcblx0XHR2YXIgdGVzdDMgPSB7fTtcblx0XHQnYWJjZGVmZ2hpamtsbW5vcHFyc3QnLnNwbGl0KCcnKS5mb3JFYWNoKGZ1bmN0aW9uIChsZXR0ZXIpIHtcblx0XHRcdHRlc3QzW2xldHRlcl0gPSBsZXR0ZXI7XG5cdFx0fSk7XG5cdFx0aWYgKE9iamVjdC5rZXlzKE9iamVjdC5hc3NpZ24oe30sIHRlc3QzKSkuam9pbignJykgIT09XG5cdFx0XHRcdCdhYmNkZWZnaGlqa2xtbm9wcXJzdCcpIHtcblx0XHRcdHJldHVybiBmYWxzZTtcblx0XHR9XG5cblx0XHRyZXR1cm4gdHJ1ZTtcblx0fSBjYXRjaCAoZXJyKSB7XG5cdFx0Ly8gV2UgZG9uJ3QgZXhwZWN0IGFueSBvZiB0aGUgYWJvdmUgdG8gdGhyb3csIGJ1dCBiZXR0ZXIgdG8gYmUgc2FmZS5cblx0XHRyZXR1cm4gZmFsc2U7XG5cdH1cbn1cblxubW9kdWxlLmV4cG9ydHMgPSBzaG91bGRVc2VOYXRpdmUoKSA/IE9iamVjdC5hc3NpZ24gOiBmdW5jdGlvbiAodGFyZ2V0LCBzb3VyY2UpIHtcblx0dmFyIGZyb207XG5cdHZhciB0byA9IHRvT2JqZWN0KHRhcmdldCk7XG5cdHZhciBzeW1ib2xzO1xuXG5cdGZvciAodmFyIHMgPSAxOyBzIDwgYXJndW1lbnRzLmxlbmd0aDsgcysrKSB7XG5cdFx0ZnJvbSA9IE9iamVjdChhcmd1bWVudHNbc10pO1xuXG5cdFx0Zm9yICh2YXIga2V5IGluIGZyb20pIHtcblx0XHRcdGlmIChoYXNPd25Qcm9wZXJ0eS5jYWxsKGZyb20sIGtleSkpIHtcblx0XHRcdFx0dG9ba2V5XSA9IGZyb21ba2V5XTtcblx0XHRcdH1cblx0XHR9XG5cblx0XHRpZiAoZ2V0T3duUHJvcGVydHlTeW1ib2xzKSB7XG5cdFx0XHRzeW1ib2xzID0gZ2V0T3duUHJvcGVydHlTeW1ib2xzKGZyb20pO1xuXHRcdFx0Zm9yICh2YXIgaSA9IDA7IGkgPCBzeW1ib2xzLmxlbmd0aDsgaSsrKSB7XG5cdFx0XHRcdGlmIChwcm9wSXNFbnVtZXJhYmxlLmNhbGwoZnJvbSwgc3ltYm9sc1tpXSkpIHtcblx0XHRcdFx0XHR0b1tzeW1ib2xzW2ldXSA9IGZyb21bc3ltYm9sc1tpXV07XG5cdFx0XHRcdH1cblx0XHRcdH1cblx0XHR9XG5cdH1cblxuXHRyZXR1cm4gdG87XG59O1xuIiwiLyoqXG4gKiBDb3B5cmlnaHQgKGMpIDIwMTMtcHJlc2VudCwgRmFjZWJvb2ssIEluYy5cbiAqXG4gKiBUaGlzIHNvdXJjZSBjb2RlIGlzIGxpY2Vuc2VkIHVuZGVyIHRoZSBNSVQgbGljZW5zZSBmb3VuZCBpbiB0aGVcbiAqIExJQ0VOU0UgZmlsZSBpbiB0aGUgcm9vdCBkaXJlY3Rvcnkgb2YgdGhpcyBzb3VyY2UgdHJlZS5cbiAqL1xuXG4ndXNlIHN0cmljdCc7XG5cbnZhciBSZWFjdFByb3BUeXBlc1NlY3JldCA9ICdTRUNSRVRfRE9fTk9UX1BBU1NfVEhJU19PUl9ZT1VfV0lMTF9CRV9GSVJFRCc7XG5cbm1vZHVsZS5leHBvcnRzID0gUmVhY3RQcm9wVHlwZXNTZWNyZXQ7XG4iLCJtb2R1bGUuZXhwb3J0cyA9IEZ1bmN0aW9uLmNhbGwuYmluZChPYmplY3QucHJvdG90eXBlLmhhc093blByb3BlcnR5KTtcbiIsIi8qKlxuICogQ29weXJpZ2h0IChjKSAyMDEzLXByZXNlbnQsIEZhY2Vib29rLCBJbmMuXG4gKlxuICogVGhpcyBzb3VyY2UgY29kZSBpcyBsaWNlbnNlZCB1bmRlciB0aGUgTUlUIGxpY2Vuc2UgZm91bmQgaW4gdGhlXG4gKiBMSUNFTlNFIGZpbGUgaW4gdGhlIHJvb3QgZGlyZWN0b3J5IG9mIHRoaXMgc291cmNlIHRyZWUuXG4gKi9cblxuJ3VzZSBzdHJpY3QnO1xuXG52YXIgcHJpbnRXYXJuaW5nID0gZnVuY3Rpb24oKSB7fTtcblxuaWYgKHByb2Nlc3MuZW52Lk5PREVfRU5WICE9PSAncHJvZHVjdGlvbicpIHtcbiAgdmFyIFJlYWN0UHJvcFR5cGVzU2VjcmV0ID0gcmVxdWlyZSgnLi9saWIvUmVhY3RQcm9wVHlwZXNTZWNyZXQnKTtcbiAgdmFyIGxvZ2dlZFR5cGVGYWlsdXJlcyA9IHt9O1xuICB2YXIgaGFzID0gcmVxdWlyZSgnLi9saWIvaGFzJyk7XG5cbiAgcHJpbnRXYXJuaW5nID0gZnVuY3Rpb24odGV4dCkge1xuICAgIHZhciBtZXNzYWdlID0gJ1dhcm5pbmc6ICcgKyB0ZXh0O1xuICAgIGlmICh0eXBlb2YgY29uc29sZSAhPT0gJ3VuZGVmaW5lZCcpIHtcbiAgICAgIGNvbnNvbGUuZXJyb3IobWVzc2FnZSk7XG4gICAgfVxuICAgIHRyeSB7XG4gICAgICAvLyAtLS0gV2VsY29tZSB0byBkZWJ1Z2dpbmcgUmVhY3QgLS0tXG4gICAgICAvLyBUaGlzIGVycm9yIHdhcyB0aHJvd24gYXMgYSBjb252ZW5pZW5jZSBzbyB0aGF0IHlvdSBjYW4gdXNlIHRoaXMgc3RhY2tcbiAgICAgIC8vIHRvIGZpbmQgdGhlIGNhbGxzaXRlIHRoYXQgY2F1c2VkIHRoaXMgd2FybmluZyB0byBmaXJlLlxuICAgICAgdGhyb3cgbmV3IEVycm9yKG1lc3NhZ2UpO1xuICAgIH0gY2F0Y2ggKHgpIHsgLyoqLyB9XG4gIH07XG59XG5cbi8qKlxuICogQXNzZXJ0IHRoYXQgdGhlIHZhbHVlcyBtYXRjaCB3aXRoIHRoZSB0eXBlIHNwZWNzLlxuICogRXJyb3IgbWVzc2FnZXMgYXJlIG1lbW9yaXplZCBhbmQgd2lsbCBvbmx5IGJlIHNob3duIG9uY2UuXG4gKlxuICogQHBhcmFtIHtvYmplY3R9IHR5cGVTcGVjcyBNYXAgb2YgbmFtZSB0byBhIFJlYWN0UHJvcFR5cGVcbiAqIEBwYXJhbSB7b2JqZWN0fSB2YWx1ZXMgUnVudGltZSB2YWx1ZXMgdGhhdCBuZWVkIHRvIGJlIHR5cGUtY2hlY2tlZFxuICogQHBhcmFtIHtzdHJpbmd9IGxvY2F0aW9uIGUuZy4gXCJwcm9wXCIsIFwiY29udGV4dFwiLCBcImNoaWxkIGNvbnRleHRcIlxuICogQHBhcmFtIHtzdHJpbmd9IGNvbXBvbmVudE5hbWUgTmFtZSBvZiB0aGUgY29tcG9uZW50IGZvciBlcnJvciBtZXNzYWdlcy5cbiAqIEBwYXJhbSB7P0Z1bmN0aW9ufSBnZXRTdGFjayBSZXR1cm5zIHRoZSBjb21wb25lbnQgc3RhY2suXG4gKiBAcHJpdmF0ZVxuICovXG5mdW5jdGlvbiBjaGVja1Byb3BUeXBlcyh0eXBlU3BlY3MsIHZhbHVlcywgbG9jYXRpb24sIGNvbXBvbmVudE5hbWUsIGdldFN0YWNrKSB7XG4gIGlmIChwcm9jZXNzLmVudi5OT0RFX0VOViAhPT0gJ3Byb2R1Y3Rpb24nKSB7XG4gICAgZm9yICh2YXIgdHlwZVNwZWNOYW1lIGluIHR5cGVTcGVjcykge1xuICAgICAgaWYgKGhhcyh0eXBlU3BlY3MsIHR5cGVTcGVjTmFtZSkpIHtcbiAgICAgICAgdmFyIGVycm9yO1xuICAgICAgICAvLyBQcm9wIHR5cGUgdmFsaWRhdGlvbiBtYXkgdGhyb3cuIEluIGNhc2UgdGhleSBkbywgd2UgZG9uJ3Qgd2FudCB0b1xuICAgICAgICAvLyBmYWlsIHRoZSByZW5kZXIgcGhhc2Ugd2hlcmUgaXQgZGlkbid0IGZhaWwgYmVmb3JlLiBTbyB3ZSBsb2cgaXQuXG4gICAgICAgIC8vIEFmdGVyIHRoZXNlIGhhdmUgYmVlbiBjbGVhbmVkIHVwLCB3ZSdsbCBsZXQgdGhlbSB0aHJvdy5cbiAgICAgICAgdHJ5IHtcbiAgICAgICAgICAvLyBUaGlzIGlzIGludGVudGlvbmFsbHkgYW4gaW52YXJpYW50IHRoYXQgZ2V0cyBjYXVnaHQuIEl0J3MgdGhlIHNhbWVcbiAgICAgICAgICAvLyBiZWhhdmlvciBhcyB3aXRob3V0IHRoaXMgc3RhdGVtZW50IGV4Y2VwdCB3aXRoIGEgYmV0dGVyIG1lc3NhZ2UuXG4gICAgICAgICAgaWYgKHR5cGVvZiB0eXBlU3BlY3NbdHlwZVNwZWNOYW1lXSAhPT0gJ2Z1bmN0aW9uJykge1xuICAgICAgICAgICAgdmFyIGVyciA9IEVycm9yKFxuICAgICAgICAgICAgICAoY29tcG9uZW50TmFtZSB8fCAnUmVhY3QgY2xhc3MnKSArICc6ICcgKyBsb2NhdGlvbiArICcgdHlwZSBgJyArIHR5cGVTcGVjTmFtZSArICdgIGlzIGludmFsaWQ7ICcgK1xuICAgICAgICAgICAgICAnaXQgbXVzdCBiZSBhIGZ1bmN0aW9uLCB1c3VhbGx5IGZyb20gdGhlIGBwcm9wLXR5cGVzYCBwYWNrYWdlLCBidXQgcmVjZWl2ZWQgYCcgKyB0eXBlb2YgdHlwZVNwZWNzW3R5cGVTcGVjTmFtZV0gKyAnYC4nICtcbiAgICAgICAgICAgICAgJ1RoaXMgb2Z0ZW4gaGFwcGVucyBiZWNhdXNlIG9mIHR5cG9zIHN1Y2ggYXMgYFByb3BUeXBlcy5mdW5jdGlvbmAgaW5zdGVhZCBvZiBgUHJvcFR5cGVzLmZ1bmNgLidcbiAgICAgICAgICAgICk7XG4gICAgICAgICAgICBlcnIubmFtZSA9ICdJbnZhcmlhbnQgVmlvbGF0aW9uJztcbiAgICAgICAgICAgIHRocm93IGVycjtcbiAgICAgICAgICB9XG4gICAgICAgICAgZXJyb3IgPSB0eXBlU3BlY3NbdHlwZVNwZWNOYW1lXSh2YWx1ZXMsIHR5cGVTcGVjTmFtZSwgY29tcG9uZW50TmFtZSwgbG9jYXRpb24sIG51bGwsIFJlYWN0UHJvcFR5cGVzU2VjcmV0KTtcbiAgICAgICAgfSBjYXRjaCAoZXgpIHtcbiAgICAgICAgICBlcnJvciA9IGV4O1xuICAgICAgICB9XG4gICAgICAgIGlmIChlcnJvciAmJiAhKGVycm9yIGluc3RhbmNlb2YgRXJyb3IpKSB7XG4gICAgICAgICAgcHJpbnRXYXJuaW5nKFxuICAgICAgICAgICAgKGNvbXBvbmVudE5hbWUgfHwgJ1JlYWN0IGNsYXNzJykgKyAnOiB0eXBlIHNwZWNpZmljYXRpb24gb2YgJyArXG4gICAgICAgICAgICBsb2NhdGlvbiArICcgYCcgKyB0eXBlU3BlY05hbWUgKyAnYCBpcyBpbnZhbGlkOyB0aGUgdHlwZSBjaGVja2VyICcgK1xuICAgICAgICAgICAgJ2Z1bmN0aW9uIG11c3QgcmV0dXJuIGBudWxsYCBvciBhbiBgRXJyb3JgIGJ1dCByZXR1cm5lZCBhICcgKyB0eXBlb2YgZXJyb3IgKyAnLiAnICtcbiAgICAgICAgICAgICdZb3UgbWF5IGhhdmUgZm9yZ290dGVuIHRvIHBhc3MgYW4gYXJndW1lbnQgdG8gdGhlIHR5cGUgY2hlY2tlciAnICtcbiAgICAgICAgICAgICdjcmVhdG9yIChhcnJheU9mLCBpbnN0YW5jZU9mLCBvYmplY3RPZiwgb25lT2YsIG9uZU9mVHlwZSwgYW5kICcgK1xuICAgICAgICAgICAgJ3NoYXBlIGFsbCByZXF1aXJlIGFuIGFyZ3VtZW50KS4nXG4gICAgICAgICAgKTtcbiAgICAgICAgfVxuICAgICAgICBpZiAoZXJyb3IgaW5zdGFuY2VvZiBFcnJvciAmJiAhKGVycm9yLm1lc3NhZ2UgaW4gbG9nZ2VkVHlwZUZhaWx1cmVzKSkge1xuICAgICAgICAgIC8vIE9ubHkgbW9uaXRvciB0aGlzIGZhaWx1cmUgb25jZSBiZWNhdXNlIHRoZXJlIHRlbmRzIHRvIGJlIGEgbG90IG9mIHRoZVxuICAgICAgICAgIC8vIHNhbWUgZXJyb3IuXG4gICAgICAgICAgbG9nZ2VkVHlwZUZhaWx1cmVzW2Vycm9yLm1lc3NhZ2VdID0gdHJ1ZTtcblxuICAgICAgICAgIHZhciBzdGFjayA9IGdldFN0YWNrID8gZ2V0U3RhY2soKSA6ICcnO1xuXG4gICAgICAgICAgcHJpbnRXYXJuaW5nKFxuICAgICAgICAgICAgJ0ZhaWxlZCAnICsgbG9jYXRpb24gKyAnIHR5cGU6ICcgKyBlcnJvci5tZXNzYWdlICsgKHN0YWNrICE9IG51bGwgPyBzdGFjayA6ICcnKVxuICAgICAgICAgICk7XG4gICAgICAgIH1cbiAgICAgIH1cbiAgICB9XG4gIH1cbn1cblxuLyoqXG4gKiBSZXNldHMgd2FybmluZyBjYWNoZSB3aGVuIHRlc3RpbmcuXG4gKlxuICogQHByaXZhdGVcbiAqL1xuY2hlY2tQcm9wVHlwZXMucmVzZXRXYXJuaW5nQ2FjaGUgPSBmdW5jdGlvbigpIHtcbiAgaWYgKHByb2Nlc3MuZW52Lk5PREVfRU5WICE9PSAncHJvZHVjdGlvbicpIHtcbiAgICBsb2dnZWRUeXBlRmFpbHVyZXMgPSB7fTtcbiAgfVxufVxuXG5tb2R1bGUuZXhwb3J0cyA9IGNoZWNrUHJvcFR5cGVzO1xuIiwiLyoqXG4gKiBDb3B5cmlnaHQgKGMpIDIwMTMtcHJlc2VudCwgRmFjZWJvb2ssIEluYy5cbiAqXG4gKiBUaGlzIHNvdXJjZSBjb2RlIGlzIGxpY2Vuc2VkIHVuZGVyIHRoZSBNSVQgbGljZW5zZSBmb3VuZCBpbiB0aGVcbiAqIExJQ0VOU0UgZmlsZSBpbiB0aGUgcm9vdCBkaXJlY3Rvcnkgb2YgdGhpcyBzb3VyY2UgdHJlZS5cbiAqL1xuXG4ndXNlIHN0cmljdCc7XG5cbnZhciBSZWFjdElzID0gcmVxdWlyZSgncmVhY3QtaXMnKTtcbnZhciBhc3NpZ24gPSByZXF1aXJlKCdvYmplY3QtYXNzaWduJyk7XG5cbnZhciBSZWFjdFByb3BUeXBlc1NlY3JldCA9IHJlcXVpcmUoJy4vbGliL1JlYWN0UHJvcFR5cGVzU2VjcmV0Jyk7XG52YXIgaGFzID0gcmVxdWlyZSgnLi9saWIvaGFzJyk7XG52YXIgY2hlY2tQcm9wVHlwZXMgPSByZXF1aXJlKCcuL2NoZWNrUHJvcFR5cGVzJyk7XG5cbnZhciBwcmludFdhcm5pbmcgPSBmdW5jdGlvbigpIHt9O1xuXG5pZiAocHJvY2Vzcy5lbnYuTk9ERV9FTlYgIT09ICdwcm9kdWN0aW9uJykge1xuICBwcmludFdhcm5pbmcgPSBmdW5jdGlvbih0ZXh0KSB7XG4gICAgdmFyIG1lc3NhZ2UgPSAnV2FybmluZzogJyArIHRleHQ7XG4gICAgaWYgKHR5cGVvZiBjb25zb2xlICE9PSAndW5kZWZpbmVkJykge1xuICAgICAgY29uc29sZS5lcnJvcihtZXNzYWdlKTtcbiAgICB9XG4gICAgdHJ5IHtcbiAgICAgIC8vIC0tLSBXZWxjb21lIHRvIGRlYnVnZ2luZyBSZWFjdCAtLS1cbiAgICAgIC8vIFRoaXMgZXJyb3Igd2FzIHRocm93biBhcyBhIGNvbnZlbmllbmNlIHNvIHRoYXQgeW91IGNhbiB1c2UgdGhpcyBzdGFja1xuICAgICAgLy8gdG8gZmluZCB0aGUgY2FsbHNpdGUgdGhhdCBjYXVzZWQgdGhpcyB3YXJuaW5nIHRvIGZpcmUuXG4gICAgICB0aHJvdyBuZXcgRXJyb3IobWVzc2FnZSk7XG4gICAgfSBjYXRjaCAoeCkge31cbiAgfTtcbn1cblxuZnVuY3Rpb24gZW1wdHlGdW5jdGlvblRoYXRSZXR1cm5zTnVsbCgpIHtcbiAgcmV0dXJuIG51bGw7XG59XG5cbm1vZHVsZS5leHBvcnRzID0gZnVuY3Rpb24oaXNWYWxpZEVsZW1lbnQsIHRocm93T25EaXJlY3RBY2Nlc3MpIHtcbiAgLyogZ2xvYmFsIFN5bWJvbCAqL1xuICB2YXIgSVRFUkFUT1JfU1lNQk9MID0gdHlwZW9mIFN5bWJvbCA9PT0gJ2Z1bmN0aW9uJyAmJiBTeW1ib2wuaXRlcmF0b3I7XG4gIHZhciBGQVVYX0lURVJBVE9SX1NZTUJPTCA9ICdAQGl0ZXJhdG9yJzsgLy8gQmVmb3JlIFN5bWJvbCBzcGVjLlxuXG4gIC8qKlxuICAgKiBSZXR1cm5zIHRoZSBpdGVyYXRvciBtZXRob2QgZnVuY3Rpb24gY29udGFpbmVkIG9uIHRoZSBpdGVyYWJsZSBvYmplY3QuXG4gICAqXG4gICAqIEJlIHN1cmUgdG8gaW52b2tlIHRoZSBmdW5jdGlvbiB3aXRoIHRoZSBpdGVyYWJsZSBhcyBjb250ZXh0OlxuICAgKlxuICAgKiAgICAgdmFyIGl0ZXJhdG9yRm4gPSBnZXRJdGVyYXRvckZuKG15SXRlcmFibGUpO1xuICAgKiAgICAgaWYgKGl0ZXJhdG9yRm4pIHtcbiAgICogICAgICAgdmFyIGl0ZXJhdG9yID0gaXRlcmF0b3JGbi5jYWxsKG15SXRlcmFibGUpO1xuICAgKiAgICAgICAuLi5cbiAgICogICAgIH1cbiAgICpcbiAgICogQHBhcmFtIHs/b2JqZWN0fSBtYXliZUl0ZXJhYmxlXG4gICAqIEByZXR1cm4gez9mdW5jdGlvbn1cbiAgICovXG4gIGZ1bmN0aW9uIGdldEl0ZXJhdG9yRm4obWF5YmVJdGVyYWJsZSkge1xuICAgIHZhciBpdGVyYXRvckZuID0gbWF5YmVJdGVyYWJsZSAmJiAoSVRFUkFUT1JfU1lNQk9MICYmIG1heWJlSXRlcmFibGVbSVRFUkFUT1JfU1lNQk9MXSB8fCBtYXliZUl0ZXJhYmxlW0ZBVVhfSVRFUkFUT1JfU1lNQk9MXSk7XG4gICAgaWYgKHR5cGVvZiBpdGVyYXRvckZuID09PSAnZnVuY3Rpb24nKSB7XG4gICAgICByZXR1cm4gaXRlcmF0b3JGbjtcbiAgICB9XG4gIH1cblxuICAvKipcbiAgICogQ29sbGVjdGlvbiBvZiBtZXRob2RzIHRoYXQgYWxsb3cgZGVjbGFyYXRpb24gYW5kIHZhbGlkYXRpb24gb2YgcHJvcHMgdGhhdCBhcmVcbiAgICogc3VwcGxpZWQgdG8gUmVhY3QgY29tcG9uZW50cy4gRXhhbXBsZSB1c2FnZTpcbiAgICpcbiAgICogICB2YXIgUHJvcHMgPSByZXF1aXJlKCdSZWFjdFByb3BUeXBlcycpO1xuICAgKiAgIHZhciBNeUFydGljbGUgPSBSZWFjdC5jcmVhdGVDbGFzcyh7XG4gICAqICAgICBwcm9wVHlwZXM6IHtcbiAgICogICAgICAgLy8gQW4gb3B0aW9uYWwgc3RyaW5nIHByb3AgbmFtZWQgXCJkZXNjcmlwdGlvblwiLlxuICAgKiAgICAgICBkZXNjcmlwdGlvbjogUHJvcHMuc3RyaW5nLFxuICAgKlxuICAgKiAgICAgICAvLyBBIHJlcXVpcmVkIGVudW0gcHJvcCBuYW1lZCBcImNhdGVnb3J5XCIuXG4gICAqICAgICAgIGNhdGVnb3J5OiBQcm9wcy5vbmVPZihbJ05ld3MnLCdQaG90b3MnXSkuaXNSZXF1aXJlZCxcbiAgICpcbiAgICogICAgICAgLy8gQSBwcm9wIG5hbWVkIFwiZGlhbG9nXCIgdGhhdCByZXF1aXJlcyBhbiBpbnN0YW5jZSBvZiBEaWFsb2cuXG4gICAqICAgICAgIGRpYWxvZzogUHJvcHMuaW5zdGFuY2VPZihEaWFsb2cpLmlzUmVxdWlyZWRcbiAgICogICAgIH0sXG4gICAqICAgICByZW5kZXI6IGZ1bmN0aW9uKCkgeyAuLi4gfVxuICAgKiAgIH0pO1xuICAgKlxuICAgKiBBIG1vcmUgZm9ybWFsIHNwZWNpZmljYXRpb24gb2YgaG93IHRoZXNlIG1ldGhvZHMgYXJlIHVzZWQ6XG4gICAqXG4gICAqICAgdHlwZSA6PSBhcnJheXxib29sfGZ1bmN8b2JqZWN0fG51bWJlcnxzdHJpbmd8b25lT2YoWy4uLl0pfGluc3RhbmNlT2YoLi4uKVxuICAgKiAgIGRlY2wgOj0gUmVhY3RQcm9wVHlwZXMue3R5cGV9KC5pc1JlcXVpcmVkKT9cbiAgICpcbiAgICogRWFjaCBhbmQgZXZlcnkgZGVjbGFyYXRpb24gcHJvZHVjZXMgYSBmdW5jdGlvbiB3aXRoIHRoZSBzYW1lIHNpZ25hdHVyZS4gVGhpc1xuICAgKiBhbGxvd3MgdGhlIGNyZWF0aW9uIG9mIGN1c3RvbSB2YWxpZGF0aW9uIGZ1bmN0aW9ucy4gRm9yIGV4YW1wbGU6XG4gICAqXG4gICAqICB2YXIgTXlMaW5rID0gUmVhY3QuY3JlYXRlQ2xhc3Moe1xuICAgKiAgICBwcm9wVHlwZXM6IHtcbiAgICogICAgICAvLyBBbiBvcHRpb25hbCBzdHJpbmcgb3IgVVJJIHByb3AgbmFtZWQgXCJocmVmXCIuXG4gICAqICAgICAgaHJlZjogZnVuY3Rpb24ocHJvcHMsIHByb3BOYW1lLCBjb21wb25lbnROYW1lKSB7XG4gICAqICAgICAgICB2YXIgcHJvcFZhbHVlID0gcHJvcHNbcHJvcE5hbWVdO1xuICAgKiAgICAgICAgaWYgKHByb3BWYWx1ZSAhPSBudWxsICYmIHR5cGVvZiBwcm9wVmFsdWUgIT09ICdzdHJpbmcnICYmXG4gICAqICAgICAgICAgICAgIShwcm9wVmFsdWUgaW5zdGFuY2VvZiBVUkkpKSB7XG4gICAqICAgICAgICAgIHJldHVybiBuZXcgRXJyb3IoXG4gICAqICAgICAgICAgICAgJ0V4cGVjdGVkIGEgc3RyaW5nIG9yIGFuIFVSSSBmb3IgJyArIHByb3BOYW1lICsgJyBpbiAnICtcbiAgICogICAgICAgICAgICBjb21wb25lbnROYW1lXG4gICAqICAgICAgICAgICk7XG4gICAqICAgICAgICB9XG4gICAqICAgICAgfVxuICAgKiAgICB9LFxuICAgKiAgICByZW5kZXI6IGZ1bmN0aW9uKCkgey4uLn1cbiAgICogIH0pO1xuICAgKlxuICAgKiBAaW50ZXJuYWxcbiAgICovXG5cbiAgdmFyIEFOT05ZTU9VUyA9ICc8PGFub255bW91cz4+JztcblxuICAvLyBJbXBvcnRhbnQhXG4gIC8vIEtlZXAgdGhpcyBsaXN0IGluIHN5bmMgd2l0aCBwcm9kdWN0aW9uIHZlcnNpb24gaW4gYC4vZmFjdG9yeVdpdGhUaHJvd2luZ1NoaW1zLmpzYC5cbiAgdmFyIFJlYWN0UHJvcFR5cGVzID0ge1xuICAgIGFycmF5OiBjcmVhdGVQcmltaXRpdmVUeXBlQ2hlY2tlcignYXJyYXknKSxcbiAgICBiaWdpbnQ6IGNyZWF0ZVByaW1pdGl2ZVR5cGVDaGVja2VyKCdiaWdpbnQnKSxcbiAgICBib29sOiBjcmVhdGVQcmltaXRpdmVUeXBlQ2hlY2tlcignYm9vbGVhbicpLFxuICAgIGZ1bmM6IGNyZWF0ZVByaW1pdGl2ZVR5cGVDaGVja2VyKCdmdW5jdGlvbicpLFxuICAgIG51bWJlcjogY3JlYXRlUHJpbWl0aXZlVHlwZUNoZWNrZXIoJ251bWJlcicpLFxuICAgIG9iamVjdDogY3JlYXRlUHJpbWl0aXZlVHlwZUNoZWNrZXIoJ29iamVjdCcpLFxuICAgIHN0cmluZzogY3JlYXRlUHJpbWl0aXZlVHlwZUNoZWNrZXIoJ3N0cmluZycpLFxuICAgIHN5bWJvbDogY3JlYXRlUHJpbWl0aXZlVHlwZUNoZWNrZXIoJ3N5bWJvbCcpLFxuXG4gICAgYW55OiBjcmVhdGVBbnlUeXBlQ2hlY2tlcigpLFxuICAgIGFycmF5T2Y6IGNyZWF0ZUFycmF5T2ZUeXBlQ2hlY2tlcixcbiAgICBlbGVtZW50OiBjcmVhdGVFbGVtZW50VHlwZUNoZWNrZXIoKSxcbiAgICBlbGVtZW50VHlwZTogY3JlYXRlRWxlbWVudFR5cGVUeXBlQ2hlY2tlcigpLFxuICAgIGluc3RhbmNlT2Y6IGNyZWF0ZUluc3RhbmNlVHlwZUNoZWNrZXIsXG4gICAgbm9kZTogY3JlYXRlTm9kZUNoZWNrZXIoKSxcbiAgICBvYmplY3RPZjogY3JlYXRlT2JqZWN0T2ZUeXBlQ2hlY2tlcixcbiAgICBvbmVPZjogY3JlYXRlRW51bVR5cGVDaGVja2VyLFxuICAgIG9uZU9mVHlwZTogY3JlYXRlVW5pb25UeXBlQ2hlY2tlcixcbiAgICBzaGFwZTogY3JlYXRlU2hhcGVUeXBlQ2hlY2tlcixcbiAgICBleGFjdDogY3JlYXRlU3RyaWN0U2hhcGVUeXBlQ2hlY2tlcixcbiAgfTtcblxuICAvKipcbiAgICogaW5saW5lZCBPYmplY3QuaXMgcG9seWZpbGwgdG8gYXZvaWQgcmVxdWlyaW5nIGNvbnN1bWVycyBzaGlwIHRoZWlyIG93blxuICAgKiBodHRwczovL2RldmVsb3Blci5tb3ppbGxhLm9yZy9lbi1VUy9kb2NzL1dlYi9KYXZhU2NyaXB0L1JlZmVyZW5jZS9HbG9iYWxfT2JqZWN0cy9PYmplY3QvaXNcbiAgICovXG4gIC8qZXNsaW50LWRpc2FibGUgbm8tc2VsZi1jb21wYXJlKi9cbiAgZnVuY3Rpb24gaXMoeCwgeSkge1xuICAgIC8vIFNhbWVWYWx1ZSBhbGdvcml0aG1cbiAgICBpZiAoeCA9PT0geSkge1xuICAgICAgLy8gU3RlcHMgMS01LCA3LTEwXG4gICAgICAvLyBTdGVwcyA2LmItNi5lOiArMCAhPSAtMFxuICAgICAgcmV0dXJuIHggIT09IDAgfHwgMSAvIHggPT09IDEgLyB5O1xuICAgIH0gZWxzZSB7XG4gICAgICAvLyBTdGVwIDYuYTogTmFOID09IE5hTlxuICAgICAgcmV0dXJuIHggIT09IHggJiYgeSAhPT0geTtcbiAgICB9XG4gIH1cbiAgLyplc2xpbnQtZW5hYmxlIG5vLXNlbGYtY29tcGFyZSovXG5cbiAgLyoqXG4gICAqIFdlIHVzZSBhbiBFcnJvci1saWtlIG9iamVjdCBmb3IgYmFja3dhcmQgY29tcGF0aWJpbGl0eSBhcyBwZW9wbGUgbWF5IGNhbGxcbiAgICogUHJvcFR5cGVzIGRpcmVjdGx5IGFuZCBpbnNwZWN0IHRoZWlyIG91dHB1dC4gSG93ZXZlciwgd2UgZG9uJ3QgdXNlIHJlYWxcbiAgICogRXJyb3JzIGFueW1vcmUuIFdlIGRvbid0IGluc3BlY3QgdGhlaXIgc3RhY2sgYW55d2F5LCBhbmQgY3JlYXRpbmcgdGhlbVxuICAgKiBpcyBwcm9oaWJpdGl2ZWx5IGV4cGVuc2l2ZSBpZiB0aGV5IGFyZSBjcmVhdGVkIHRvbyBvZnRlbiwgc3VjaCBhcyB3aGF0XG4gICAqIGhhcHBlbnMgaW4gb25lT2ZUeXBlKCkgZm9yIGFueSB0eXBlIGJlZm9yZSB0aGUgb25lIHRoYXQgbWF0Y2hlZC5cbiAgICovXG4gIGZ1bmN0aW9uIFByb3BUeXBlRXJyb3IobWVzc2FnZSwgZGF0YSkge1xuICAgIHRoaXMubWVzc2FnZSA9IG1lc3NhZ2U7XG4gICAgdGhpcy5kYXRhID0gZGF0YSAmJiB0eXBlb2YgZGF0YSA9PT0gJ29iamVjdCcgPyBkYXRhOiB7fTtcbiAgICB0aGlzLnN0YWNrID0gJyc7XG4gIH1cbiAgLy8gTWFrZSBgaW5zdGFuY2VvZiBFcnJvcmAgc3RpbGwgd29yayBmb3IgcmV0dXJuZWQgZXJyb3JzLlxuICBQcm9wVHlwZUVycm9yLnByb3RvdHlwZSA9IEVycm9yLnByb3RvdHlwZTtcblxuICBmdW5jdGlvbiBjcmVhdGVDaGFpbmFibGVUeXBlQ2hlY2tlcih2YWxpZGF0ZSkge1xuICAgIGlmIChwcm9jZXNzLmVudi5OT0RFX0VOViAhPT0gJ3Byb2R1Y3Rpb24nKSB7XG4gICAgICB2YXIgbWFudWFsUHJvcFR5cGVDYWxsQ2FjaGUgPSB7fTtcbiAgICAgIHZhciBtYW51YWxQcm9wVHlwZVdhcm5pbmdDb3VudCA9IDA7XG4gICAgfVxuICAgIGZ1bmN0aW9uIGNoZWNrVHlwZShpc1JlcXVpcmVkLCBwcm9wcywgcHJvcE5hbWUsIGNvbXBvbmVudE5hbWUsIGxvY2F0aW9uLCBwcm9wRnVsbE5hbWUsIHNlY3JldCkge1xuICAgICAgY29tcG9uZW50TmFtZSA9IGNvbXBvbmVudE5hbWUgfHwgQU5PTllNT1VTO1xuICAgICAgcHJvcEZ1bGxOYW1lID0gcHJvcEZ1bGxOYW1lIHx8IHByb3BOYW1lO1xuXG4gICAgICBpZiAoc2VjcmV0ICE9PSBSZWFjdFByb3BUeXBlc1NlY3JldCkge1xuICAgICAgICBpZiAodGhyb3dPbkRpcmVjdEFjY2Vzcykge1xuICAgICAgICAgIC8vIE5ldyBiZWhhdmlvciBvbmx5IGZvciB1c2VycyBvZiBgcHJvcC10eXBlc2AgcGFja2FnZVxuICAgICAgICAgIHZhciBlcnIgPSBuZXcgRXJyb3IoXG4gICAgICAgICAgICAnQ2FsbGluZyBQcm9wVHlwZXMgdmFsaWRhdG9ycyBkaXJlY3RseSBpcyBub3Qgc3VwcG9ydGVkIGJ5IHRoZSBgcHJvcC10eXBlc2AgcGFja2FnZS4gJyArXG4gICAgICAgICAgICAnVXNlIGBQcm9wVHlwZXMuY2hlY2tQcm9wVHlwZXMoKWAgdG8gY2FsbCB0aGVtLiAnICtcbiAgICAgICAgICAgICdSZWFkIG1vcmUgYXQgaHR0cDovL2ZiLm1lL3VzZS1jaGVjay1wcm9wLXR5cGVzJ1xuICAgICAgICAgICk7XG4gICAgICAgICAgZXJyLm5hbWUgPSAnSW52YXJpYW50IFZpb2xhdGlvbic7XG4gICAgICAgICAgdGhyb3cgZXJyO1xuICAgICAgICB9IGVsc2UgaWYgKHByb2Nlc3MuZW52Lk5PREVfRU5WICE9PSAncHJvZHVjdGlvbicgJiYgdHlwZW9mIGNvbnNvbGUgIT09ICd1bmRlZmluZWQnKSB7XG4gICAgICAgICAgLy8gT2xkIGJlaGF2aW9yIGZvciBwZW9wbGUgdXNpbmcgUmVhY3QuUHJvcFR5cGVzXG4gICAgICAgICAgdmFyIGNhY2hlS2V5ID0gY29tcG9uZW50TmFtZSArICc6JyArIHByb3BOYW1lO1xuICAgICAgICAgIGlmIChcbiAgICAgICAgICAgICFtYW51YWxQcm9wVHlwZUNhbGxDYWNoZVtjYWNoZUtleV0gJiZcbiAgICAgICAgICAgIC8vIEF2b2lkIHNwYW1taW5nIHRoZSBjb25zb2xlIGJlY2F1c2UgdGhleSBhcmUgb2Z0ZW4gbm90IGFjdGlvbmFibGUgZXhjZXB0IGZvciBsaWIgYXV0aG9yc1xuICAgICAgICAgICAgbWFudWFsUHJvcFR5cGVXYXJuaW5nQ291bnQgPCAzXG4gICAgICAgICAgKSB7XG4gICAgICAgICAgICBwcmludFdhcm5pbmcoXG4gICAgICAgICAgICAgICdZb3UgYXJlIG1hbnVhbGx5IGNhbGxpbmcgYSBSZWFjdC5Qcm9wVHlwZXMgdmFsaWRhdGlvbiAnICtcbiAgICAgICAgICAgICAgJ2Z1bmN0aW9uIGZvciB0aGUgYCcgKyBwcm9wRnVsbE5hbWUgKyAnYCBwcm9wIG9uIGAnICsgY29tcG9uZW50TmFtZSArICdgLiBUaGlzIGlzIGRlcHJlY2F0ZWQgJyArXG4gICAgICAgICAgICAgICdhbmQgd2lsbCB0aHJvdyBpbiB0aGUgc3RhbmRhbG9uZSBgcHJvcC10eXBlc2AgcGFja2FnZS4gJyArXG4gICAgICAgICAgICAgICdZb3UgbWF5IGJlIHNlZWluZyB0aGlzIHdhcm5pbmcgZHVlIHRvIGEgdGhpcmQtcGFydHkgUHJvcFR5cGVzICcgK1xuICAgICAgICAgICAgICAnbGlicmFyeS4gU2VlIGh0dHBzOi8vZmIubWUvcmVhY3Qtd2FybmluZy1kb250LWNhbGwtcHJvcHR5cGVzICcgKyAnZm9yIGRldGFpbHMuJ1xuICAgICAgICAgICAgKTtcbiAgICAgICAgICAgIG1hbnVhbFByb3BUeXBlQ2FsbENhY2hlW2NhY2hlS2V5XSA9IHRydWU7XG4gICAgICAgICAgICBtYW51YWxQcm9wVHlwZVdhcm5pbmdDb3VudCsrO1xuICAgICAgICAgIH1cbiAgICAgICAgfVxuICAgICAgfVxuICAgICAgaWYgKHByb3BzW3Byb3BOYW1lXSA9PSBudWxsKSB7XG4gICAgICAgIGlmIChpc1JlcXVpcmVkKSB7XG4gICAgICAgICAgaWYgKHByb3BzW3Byb3BOYW1lXSA9PT0gbnVsbCkge1xuICAgICAgICAgICAgcmV0dXJuIG5ldyBQcm9wVHlwZUVycm9yKCdUaGUgJyArIGxvY2F0aW9uICsgJyBgJyArIHByb3BGdWxsTmFtZSArICdgIGlzIG1hcmtlZCBhcyByZXF1aXJlZCAnICsgKCdpbiBgJyArIGNvbXBvbmVudE5hbWUgKyAnYCwgYnV0IGl0cyB2YWx1ZSBpcyBgbnVsbGAuJykpO1xuICAgICAgICAgIH1cbiAgICAgICAgICByZXR1cm4gbmV3IFByb3BUeXBlRXJyb3IoJ1RoZSAnICsgbG9jYXRpb24gKyAnIGAnICsgcHJvcEZ1bGxOYW1lICsgJ2AgaXMgbWFya2VkIGFzIHJlcXVpcmVkIGluICcgKyAoJ2AnICsgY29tcG9uZW50TmFtZSArICdgLCBidXQgaXRzIHZhbHVlIGlzIGB1bmRlZmluZWRgLicpKTtcbiAgICAgICAgfVxuICAgICAgICByZXR1cm4gbnVsbDtcbiAgICAgIH0gZWxzZSB7XG4gICAgICAgIHJldHVybiB2YWxpZGF0ZShwcm9wcywgcHJvcE5hbWUsIGNvbXBvbmVudE5hbWUsIGxvY2F0aW9uLCBwcm9wRnVsbE5hbWUpO1xuICAgICAgfVxuICAgIH1cblxuICAgIHZhciBjaGFpbmVkQ2hlY2tUeXBlID0gY2hlY2tUeXBlLmJpbmQobnVsbCwgZmFsc2UpO1xuICAgIGNoYWluZWRDaGVja1R5cGUuaXNSZXF1aXJlZCA9IGNoZWNrVHlwZS5iaW5kKG51bGwsIHRydWUpO1xuXG4gICAgcmV0dXJuIGNoYWluZWRDaGVja1R5cGU7XG4gIH1cblxuICBmdW5jdGlvbiBjcmVhdGVQcmltaXRpdmVUeXBlQ2hlY2tlcihleHBlY3RlZFR5cGUpIHtcbiAgICBmdW5jdGlvbiB2YWxpZGF0ZShwcm9wcywgcHJvcE5hbWUsIGNvbXBvbmVudE5hbWUsIGxvY2F0aW9uLCBwcm9wRnVsbE5hbWUsIHNlY3JldCkge1xuICAgICAgdmFyIHByb3BWYWx1ZSA9IHByb3BzW3Byb3BOYW1lXTtcbiAgICAgIHZhciBwcm9wVHlwZSA9IGdldFByb3BUeXBlKHByb3BWYWx1ZSk7XG4gICAgICBpZiAocHJvcFR5cGUgIT09IGV4cGVjdGVkVHlwZSkge1xuICAgICAgICAvLyBgcHJvcFZhbHVlYCBiZWluZyBpbnN0YW5jZSBvZiwgc2F5LCBkYXRlL3JlZ2V4cCwgcGFzcyB0aGUgJ29iamVjdCdcbiAgICAgICAgLy8gY2hlY2ssIGJ1dCB3ZSBjYW4gb2ZmZXIgYSBtb3JlIHByZWNpc2UgZXJyb3IgbWVzc2FnZSBoZXJlIHJhdGhlciB0aGFuXG4gICAgICAgIC8vICdvZiB0eXBlIGBvYmplY3RgJy5cbiAgICAgICAgdmFyIHByZWNpc2VUeXBlID0gZ2V0UHJlY2lzZVR5cGUocHJvcFZhbHVlKTtcblxuICAgICAgICByZXR1cm4gbmV3IFByb3BUeXBlRXJyb3IoXG4gICAgICAgICAgJ0ludmFsaWQgJyArIGxvY2F0aW9uICsgJyBgJyArIHByb3BGdWxsTmFtZSArICdgIG9mIHR5cGUgJyArICgnYCcgKyBwcmVjaXNlVHlwZSArICdgIHN1cHBsaWVkIHRvIGAnICsgY29tcG9uZW50TmFtZSArICdgLCBleHBlY3RlZCAnKSArICgnYCcgKyBleHBlY3RlZFR5cGUgKyAnYC4nKSxcbiAgICAgICAgICB7ZXhwZWN0ZWRUeXBlOiBleHBlY3RlZFR5cGV9XG4gICAgICAgICk7XG4gICAgICB9XG4gICAgICByZXR1cm4gbnVsbDtcbiAgICB9XG4gICAgcmV0dXJuIGNyZWF0ZUNoYWluYWJsZVR5cGVDaGVja2VyKHZhbGlkYXRlKTtcbiAgfVxuXG4gIGZ1bmN0aW9uIGNyZWF0ZUFueVR5cGVDaGVja2VyKCkge1xuICAgIHJldHVybiBjcmVhdGVDaGFpbmFibGVUeXBlQ2hlY2tlcihlbXB0eUZ1bmN0aW9uVGhhdFJldHVybnNOdWxsKTtcbiAgfVxuXG4gIGZ1bmN0aW9uIGNyZWF0ZUFycmF5T2ZUeXBlQ2hlY2tlcih0eXBlQ2hlY2tlcikge1xuICAgIGZ1bmN0aW9uIHZhbGlkYXRlKHByb3BzLCBwcm9wTmFtZSwgY29tcG9uZW50TmFtZSwgbG9jYXRpb24sIHByb3BGdWxsTmFtZSkge1xuICAgICAgaWYgKHR5cGVvZiB0eXBlQ2hlY2tlciAhPT0gJ2Z1bmN0aW9uJykge1xuICAgICAgICByZXR1cm4gbmV3IFByb3BUeXBlRXJyb3IoJ1Byb3BlcnR5IGAnICsgcHJvcEZ1bGxOYW1lICsgJ2Agb2YgY29tcG9uZW50IGAnICsgY29tcG9uZW50TmFtZSArICdgIGhhcyBpbnZhbGlkIFByb3BUeXBlIG5vdGF0aW9uIGluc2lkZSBhcnJheU9mLicpO1xuICAgICAgfVxuICAgICAgdmFyIHByb3BWYWx1ZSA9IHByb3BzW3Byb3BOYW1lXTtcbiAgICAgIGlmICghQXJyYXkuaXNBcnJheShwcm9wVmFsdWUpKSB7XG4gICAgICAgIHZhciBwcm9wVHlwZSA9IGdldFByb3BUeXBlKHByb3BWYWx1ZSk7XG4gICAgICAgIHJldHVybiBuZXcgUHJvcFR5cGVFcnJvcignSW52YWxpZCAnICsgbG9jYXRpb24gKyAnIGAnICsgcHJvcEZ1bGxOYW1lICsgJ2Agb2YgdHlwZSAnICsgKCdgJyArIHByb3BUeXBlICsgJ2Agc3VwcGxpZWQgdG8gYCcgKyBjb21wb25lbnROYW1lICsgJ2AsIGV4cGVjdGVkIGFuIGFycmF5LicpKTtcbiAgICAgIH1cbiAgICAgIGZvciAodmFyIGkgPSAwOyBpIDwgcHJvcFZhbHVlLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgIHZhciBlcnJvciA9IHR5cGVDaGVja2VyKHByb3BWYWx1ZSwgaSwgY29tcG9uZW50TmFtZSwgbG9jYXRpb24sIHByb3BGdWxsTmFtZSArICdbJyArIGkgKyAnXScsIFJlYWN0UHJvcFR5cGVzU2VjcmV0KTtcbiAgICAgICAgaWYgKGVycm9yIGluc3RhbmNlb2YgRXJyb3IpIHtcbiAgICAgICAgICByZXR1cm4gZXJyb3I7XG4gICAgICAgIH1cbiAgICAgIH1cbiAgICAgIHJldHVybiBudWxsO1xuICAgIH1cbiAgICByZXR1cm4gY3JlYXRlQ2hhaW5hYmxlVHlwZUNoZWNrZXIodmFsaWRhdGUpO1xuICB9XG5cbiAgZnVuY3Rpb24gY3JlYXRlRWxlbWVudFR5cGVDaGVja2VyKCkge1xuICAgIGZ1bmN0aW9uIHZhbGlkYXRlKHByb3BzLCBwcm9wTmFtZSwgY29tcG9uZW50TmFtZSwgbG9jYXRpb24sIHByb3BGdWxsTmFtZSkge1xuICAgICAgdmFyIHByb3BWYWx1ZSA9IHByb3BzW3Byb3BOYW1lXTtcbiAgICAgIGlmICghaXNWYWxpZEVsZW1lbnQocHJvcFZhbHVlKSkge1xuICAgICAgICB2YXIgcHJvcFR5cGUgPSBnZXRQcm9wVHlwZShwcm9wVmFsdWUpO1xuICAgICAgICByZXR1cm4gbmV3IFByb3BUeXBlRXJyb3IoJ0ludmFsaWQgJyArIGxvY2F0aW9uICsgJyBgJyArIHByb3BGdWxsTmFtZSArICdgIG9mIHR5cGUgJyArICgnYCcgKyBwcm9wVHlwZSArICdgIHN1cHBsaWVkIHRvIGAnICsgY29tcG9uZW50TmFtZSArICdgLCBleHBlY3RlZCBhIHNpbmdsZSBSZWFjdEVsZW1lbnQuJykpO1xuICAgICAgfVxuICAgICAgcmV0dXJuIG51bGw7XG4gICAgfVxuICAgIHJldHVybiBjcmVhdGVDaGFpbmFibGVUeXBlQ2hlY2tlcih2YWxpZGF0ZSk7XG4gIH1cblxuICBmdW5jdGlvbiBjcmVhdGVFbGVtZW50VHlwZVR5cGVDaGVja2VyKCkge1xuICAgIGZ1bmN0aW9uIHZhbGlkYXRlKHByb3BzLCBwcm9wTmFtZSwgY29tcG9uZW50TmFtZSwgbG9jYXRpb24sIHByb3BGdWxsTmFtZSkge1xuICAgICAgdmFyIHByb3BWYWx1ZSA9IHByb3BzW3Byb3BOYW1lXTtcbiAgICAgIGlmICghUmVhY3RJcy5pc1ZhbGlkRWxlbWVudFR5cGUocHJvcFZhbHVlKSkge1xuICAgICAgICB2YXIgcHJvcFR5cGUgPSBnZXRQcm9wVHlwZShwcm9wVmFsdWUpO1xuICAgICAgICByZXR1cm4gbmV3IFByb3BUeXBlRXJyb3IoJ0ludmFsaWQgJyArIGxvY2F0aW9uICsgJyBgJyArIHByb3BGdWxsTmFtZSArICdgIG9mIHR5cGUgJyArICgnYCcgKyBwcm9wVHlwZSArICdgIHN1cHBsaWVkIHRvIGAnICsgY29tcG9uZW50TmFtZSArICdgLCBleHBlY3RlZCBhIHNpbmdsZSBSZWFjdEVsZW1lbnQgdHlwZS4nKSk7XG4gICAgICB9XG4gICAgICByZXR1cm4gbnVsbDtcbiAgICB9XG4gICAgcmV0dXJuIGNyZWF0ZUNoYWluYWJsZVR5cGVDaGVja2VyKHZhbGlkYXRlKTtcbiAgfVxuXG4gIGZ1bmN0aW9uIGNyZWF0ZUluc3RhbmNlVHlwZUNoZWNrZXIoZXhwZWN0ZWRDbGFzcykge1xuICAgIGZ1bmN0aW9uIHZhbGlkYXRlKHByb3BzLCBwcm9wTmFtZSwgY29tcG9uZW50TmFtZSwgbG9jYXRpb24sIHByb3BGdWxsTmFtZSkge1xuICAgICAgaWYgKCEocHJvcHNbcHJvcE5hbWVdIGluc3RhbmNlb2YgZXhwZWN0ZWRDbGFzcykpIHtcbiAgICAgICAgdmFyIGV4cGVjdGVkQ2xhc3NOYW1lID0gZXhwZWN0ZWRDbGFzcy5uYW1lIHx8IEFOT05ZTU9VUztcbiAgICAgICAgdmFyIGFjdHVhbENsYXNzTmFtZSA9IGdldENsYXNzTmFtZShwcm9wc1twcm9wTmFtZV0pO1xuICAgICAgICByZXR1cm4gbmV3IFByb3BUeXBlRXJyb3IoJ0ludmFsaWQgJyArIGxvY2F0aW9uICsgJyBgJyArIHByb3BGdWxsTmFtZSArICdgIG9mIHR5cGUgJyArICgnYCcgKyBhY3R1YWxDbGFzc05hbWUgKyAnYCBzdXBwbGllZCB0byBgJyArIGNvbXBvbmVudE5hbWUgKyAnYCwgZXhwZWN0ZWQgJykgKyAoJ2luc3RhbmNlIG9mIGAnICsgZXhwZWN0ZWRDbGFzc05hbWUgKyAnYC4nKSk7XG4gICAgICB9XG4gICAgICByZXR1cm4gbnVsbDtcbiAgICB9XG4gICAgcmV0dXJuIGNyZWF0ZUNoYWluYWJsZVR5cGVDaGVja2VyKHZhbGlkYXRlKTtcbiAgfVxuXG4gIGZ1bmN0aW9uIGNyZWF0ZUVudW1UeXBlQ2hlY2tlcihleHBlY3RlZFZhbHVlcykge1xuICAgIGlmICghQXJyYXkuaXNBcnJheShleHBlY3RlZFZhbHVlcykpIHtcbiAgICAgIGlmIChwcm9jZXNzLmVudi5OT0RFX0VOViAhPT0gJ3Byb2R1Y3Rpb24nKSB7XG4gICAgICAgIGlmIChhcmd1bWVudHMubGVuZ3RoID4gMSkge1xuICAgICAgICAgIHByaW50V2FybmluZyhcbiAgICAgICAgICAgICdJbnZhbGlkIGFyZ3VtZW50cyBzdXBwbGllZCB0byBvbmVPZiwgZXhwZWN0ZWQgYW4gYXJyYXksIGdvdCAnICsgYXJndW1lbnRzLmxlbmd0aCArICcgYXJndW1lbnRzLiAnICtcbiAgICAgICAgICAgICdBIGNvbW1vbiBtaXN0YWtlIGlzIHRvIHdyaXRlIG9uZU9mKHgsIHksIHopIGluc3RlYWQgb2Ygb25lT2YoW3gsIHksIHpdKS4nXG4gICAgICAgICAgKTtcbiAgICAgICAgfSBlbHNlIHtcbiAgICAgICAgICBwcmludFdhcm5pbmcoJ0ludmFsaWQgYXJndW1lbnQgc3VwcGxpZWQgdG8gb25lT2YsIGV4cGVjdGVkIGFuIGFycmF5LicpO1xuICAgICAgICB9XG4gICAgICB9XG4gICAgICByZXR1cm4gZW1wdHlGdW5jdGlvblRoYXRSZXR1cm5zTnVsbDtcbiAgICB9XG5cbiAgICBmdW5jdGlvbiB2YWxpZGF0ZShwcm9wcywgcHJvcE5hbWUsIGNvbXBvbmVudE5hbWUsIGxvY2F0aW9uLCBwcm9wRnVsbE5hbWUpIHtcbiAgICAgIHZhciBwcm9wVmFsdWUgPSBwcm9wc1twcm9wTmFtZV07XG4gICAgICBmb3IgKHZhciBpID0gMDsgaSA8IGV4cGVjdGVkVmFsdWVzLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgIGlmIChpcyhwcm9wVmFsdWUsIGV4cGVjdGVkVmFsdWVzW2ldKSkge1xuICAgICAgICAgIHJldHVybiBudWxsO1xuICAgICAgICB9XG4gICAgICB9XG5cbiAgICAgIHZhciB2YWx1ZXNTdHJpbmcgPSBKU09OLnN0cmluZ2lmeShleHBlY3RlZFZhbHVlcywgZnVuY3Rpb24gcmVwbGFjZXIoa2V5LCB2YWx1ZSkge1xuICAgICAgICB2YXIgdHlwZSA9IGdldFByZWNpc2VUeXBlKHZhbHVlKTtcbiAgICAgICAgaWYgKHR5cGUgPT09ICdzeW1ib2wnKSB7XG4gICAgICAgICAgcmV0dXJuIFN0cmluZyh2YWx1ZSk7XG4gICAgICAgIH1cbiAgICAgICAgcmV0dXJuIHZhbHVlO1xuICAgICAgfSk7XG4gICAgICByZXR1cm4gbmV3IFByb3BUeXBlRXJyb3IoJ0ludmFsaWQgJyArIGxvY2F0aW9uICsgJyBgJyArIHByb3BGdWxsTmFtZSArICdgIG9mIHZhbHVlIGAnICsgU3RyaW5nKHByb3BWYWx1ZSkgKyAnYCAnICsgKCdzdXBwbGllZCB0byBgJyArIGNvbXBvbmVudE5hbWUgKyAnYCwgZXhwZWN0ZWQgb25lIG9mICcgKyB2YWx1ZXNTdHJpbmcgKyAnLicpKTtcbiAgICB9XG4gICAgcmV0dXJuIGNyZWF0ZUNoYWluYWJsZVR5cGVDaGVja2VyKHZhbGlkYXRlKTtcbiAgfVxuXG4gIGZ1bmN0aW9uIGNyZWF0ZU9iamVjdE9mVHlwZUNoZWNrZXIodHlwZUNoZWNrZXIpIHtcbiAgICBmdW5jdGlvbiB2YWxpZGF0ZShwcm9wcywgcHJvcE5hbWUsIGNvbXBvbmVudE5hbWUsIGxvY2F0aW9uLCBwcm9wRnVsbE5hbWUpIHtcbiAgICAgIGlmICh0eXBlb2YgdHlwZUNoZWNrZXIgIT09ICdmdW5jdGlvbicpIHtcbiAgICAgICAgcmV0dXJuIG5ldyBQcm9wVHlwZUVycm9yKCdQcm9wZXJ0eSBgJyArIHByb3BGdWxsTmFtZSArICdgIG9mIGNvbXBvbmVudCBgJyArIGNvbXBvbmVudE5hbWUgKyAnYCBoYXMgaW52YWxpZCBQcm9wVHlwZSBub3RhdGlvbiBpbnNpZGUgb2JqZWN0T2YuJyk7XG4gICAgICB9XG4gICAgICB2YXIgcHJvcFZhbHVlID0gcHJvcHNbcHJvcE5hbWVdO1xuICAgICAgdmFyIHByb3BUeXBlID0gZ2V0UHJvcFR5cGUocHJvcFZhbHVlKTtcbiAgICAgIGlmIChwcm9wVHlwZSAhPT0gJ29iamVjdCcpIHtcbiAgICAgICAgcmV0dXJuIG5ldyBQcm9wVHlwZUVycm9yKCdJbnZhbGlkICcgKyBsb2NhdGlvbiArICcgYCcgKyBwcm9wRnVsbE5hbWUgKyAnYCBvZiB0eXBlICcgKyAoJ2AnICsgcHJvcFR5cGUgKyAnYCBzdXBwbGllZCB0byBgJyArIGNvbXBvbmVudE5hbWUgKyAnYCwgZXhwZWN0ZWQgYW4gb2JqZWN0LicpKTtcbiAgICAgIH1cbiAgICAgIGZvciAodmFyIGtleSBpbiBwcm9wVmFsdWUpIHtcbiAgICAgICAgaWYgKGhhcyhwcm9wVmFsdWUsIGtleSkpIHtcbiAgICAgICAgICB2YXIgZXJyb3IgPSB0eXBlQ2hlY2tlcihwcm9wVmFsdWUsIGtleSwgY29tcG9uZW50TmFtZSwgbG9jYXRpb24sIHByb3BGdWxsTmFtZSArICcuJyArIGtleSwgUmVhY3RQcm9wVHlwZXNTZWNyZXQpO1xuICAgICAgICAgIGlmIChlcnJvciBpbnN0YW5jZW9mIEVycm9yKSB7XG4gICAgICAgICAgICByZXR1cm4gZXJyb3I7XG4gICAgICAgICAgfVxuICAgICAgICB9XG4gICAgICB9XG4gICAgICByZXR1cm4gbnVsbDtcbiAgICB9XG4gICAgcmV0dXJuIGNyZWF0ZUNoYWluYWJsZVR5cGVDaGVja2VyKHZhbGlkYXRlKTtcbiAgfVxuXG4gIGZ1bmN0aW9uIGNyZWF0ZVVuaW9uVHlwZUNoZWNrZXIoYXJyYXlPZlR5cGVDaGVja2Vycykge1xuICAgIGlmICghQXJyYXkuaXNBcnJheShhcnJheU9mVHlwZUNoZWNrZXJzKSkge1xuICAgICAgcHJvY2Vzcy5lbnYuTk9ERV9FTlYgIT09ICdwcm9kdWN0aW9uJyA/IHByaW50V2FybmluZygnSW52YWxpZCBhcmd1bWVudCBzdXBwbGllZCB0byBvbmVPZlR5cGUsIGV4cGVjdGVkIGFuIGluc3RhbmNlIG9mIGFycmF5LicpIDogdm9pZCAwO1xuICAgICAgcmV0dXJuIGVtcHR5RnVuY3Rpb25UaGF0UmV0dXJuc051bGw7XG4gICAgfVxuXG4gICAgZm9yICh2YXIgaSA9IDA7IGkgPCBhcnJheU9mVHlwZUNoZWNrZXJzLmxlbmd0aDsgaSsrKSB7XG4gICAgICB2YXIgY2hlY2tlciA9IGFycmF5T2ZUeXBlQ2hlY2tlcnNbaV07XG4gICAgICBpZiAodHlwZW9mIGNoZWNrZXIgIT09ICdmdW5jdGlvbicpIHtcbiAgICAgICAgcHJpbnRXYXJuaW5nKFxuICAgICAgICAgICdJbnZhbGlkIGFyZ3VtZW50IHN1cHBsaWVkIHRvIG9uZU9mVHlwZS4gRXhwZWN0ZWQgYW4gYXJyYXkgb2YgY2hlY2sgZnVuY3Rpb25zLCBidXQgJyArXG4gICAgICAgICAgJ3JlY2VpdmVkICcgKyBnZXRQb3N0Zml4Rm9yVHlwZVdhcm5pbmcoY2hlY2tlcikgKyAnIGF0IGluZGV4ICcgKyBpICsgJy4nXG4gICAgICAgICk7XG4gICAgICAgIHJldHVybiBlbXB0eUZ1bmN0aW9uVGhhdFJldHVybnNOdWxsO1xuICAgICAgfVxuICAgIH1cblxuICAgIGZ1bmN0aW9uIHZhbGlkYXRlKHByb3BzLCBwcm9wTmFtZSwgY29tcG9uZW50TmFtZSwgbG9jYXRpb24sIHByb3BGdWxsTmFtZSkge1xuICAgICAgdmFyIGV4cGVjdGVkVHlwZXMgPSBbXTtcbiAgICAgIGZvciAodmFyIGkgPSAwOyBpIDwgYXJyYXlPZlR5cGVDaGVja2Vycy5sZW5ndGg7IGkrKykge1xuICAgICAgICB2YXIgY2hlY2tlciA9IGFycmF5T2ZUeXBlQ2hlY2tlcnNbaV07XG4gICAgICAgIHZhciBjaGVja2VyUmVzdWx0ID0gY2hlY2tlcihwcm9wcywgcHJvcE5hbWUsIGNvbXBvbmVudE5hbWUsIGxvY2F0aW9uLCBwcm9wRnVsbE5hbWUsIFJlYWN0UHJvcFR5cGVzU2VjcmV0KTtcbiAgICAgICAgaWYgKGNoZWNrZXJSZXN1bHQgPT0gbnVsbCkge1xuICAgICAgICAgIHJldHVybiBudWxsO1xuICAgICAgICB9XG4gICAgICAgIGlmIChjaGVja2VyUmVzdWx0LmRhdGEgJiYgaGFzKGNoZWNrZXJSZXN1bHQuZGF0YSwgJ2V4cGVjdGVkVHlwZScpKSB7XG4gICAgICAgICAgZXhwZWN0ZWRUeXBlcy5wdXNoKGNoZWNrZXJSZXN1bHQuZGF0YS5leHBlY3RlZFR5cGUpO1xuICAgICAgICB9XG4gICAgICB9XG4gICAgICB2YXIgZXhwZWN0ZWRUeXBlc01lc3NhZ2UgPSAoZXhwZWN0ZWRUeXBlcy5sZW5ndGggPiAwKSA/ICcsIGV4cGVjdGVkIG9uZSBvZiB0eXBlIFsnICsgZXhwZWN0ZWRUeXBlcy5qb2luKCcsICcpICsgJ10nOiAnJztcbiAgICAgIHJldHVybiBuZXcgUHJvcFR5cGVFcnJvcignSW52YWxpZCAnICsgbG9jYXRpb24gKyAnIGAnICsgcHJvcEZ1bGxOYW1lICsgJ2Agc3VwcGxpZWQgdG8gJyArICgnYCcgKyBjb21wb25lbnROYW1lICsgJ2AnICsgZXhwZWN0ZWRUeXBlc01lc3NhZ2UgKyAnLicpKTtcbiAgICB9XG4gICAgcmV0dXJuIGNyZWF0ZUNoYWluYWJsZVR5cGVDaGVja2VyKHZhbGlkYXRlKTtcbiAgfVxuXG4gIGZ1bmN0aW9uIGNyZWF0ZU5vZGVDaGVja2VyKCkge1xuICAgIGZ1bmN0aW9uIHZhbGlkYXRlKHByb3BzLCBwcm9wTmFtZSwgY29tcG9uZW50TmFtZSwgbG9jYXRpb24sIHByb3BGdWxsTmFtZSkge1xuICAgICAgaWYgKCFpc05vZGUocHJvcHNbcHJvcE5hbWVdKSkge1xuICAgICAgICByZXR1cm4gbmV3IFByb3BUeXBlRXJyb3IoJ0ludmFsaWQgJyArIGxvY2F0aW9uICsgJyBgJyArIHByb3BGdWxsTmFtZSArICdgIHN1cHBsaWVkIHRvICcgKyAoJ2AnICsgY29tcG9uZW50TmFtZSArICdgLCBleHBlY3RlZCBhIFJlYWN0Tm9kZS4nKSk7XG4gICAgICB9XG4gICAgICByZXR1cm4gbnVsbDtcbiAgICB9XG4gICAgcmV0dXJuIGNyZWF0ZUNoYWluYWJsZVR5cGVDaGVja2VyKHZhbGlkYXRlKTtcbiAgfVxuXG4gIGZ1bmN0aW9uIGludmFsaWRWYWxpZGF0b3JFcnJvcihjb21wb25lbnROYW1lLCBsb2NhdGlvbiwgcHJvcEZ1bGxOYW1lLCBrZXksIHR5cGUpIHtcbiAgICByZXR1cm4gbmV3IFByb3BUeXBlRXJyb3IoXG4gICAgICAoY29tcG9uZW50TmFtZSB8fCAnUmVhY3QgY2xhc3MnKSArICc6ICcgKyBsb2NhdGlvbiArICcgdHlwZSBgJyArIHByb3BGdWxsTmFtZSArICcuJyArIGtleSArICdgIGlzIGludmFsaWQ7ICcgK1xuICAgICAgJ2l0IG11c3QgYmUgYSBmdW5jdGlvbiwgdXN1YWxseSBmcm9tIHRoZSBgcHJvcC10eXBlc2AgcGFja2FnZSwgYnV0IHJlY2VpdmVkIGAnICsgdHlwZSArICdgLidcbiAgICApO1xuICB9XG5cbiAgZnVuY3Rpb24gY3JlYXRlU2hhcGVUeXBlQ2hlY2tlcihzaGFwZVR5cGVzKSB7XG4gICAgZnVuY3Rpb24gdmFsaWRhdGUocHJvcHMsIHByb3BOYW1lLCBjb21wb25lbnROYW1lLCBsb2NhdGlvbiwgcHJvcEZ1bGxOYW1lKSB7XG4gICAgICB2YXIgcHJvcFZhbHVlID0gcHJvcHNbcHJvcE5hbWVdO1xuICAgICAgdmFyIHByb3BUeXBlID0gZ2V0UHJvcFR5cGUocHJvcFZhbHVlKTtcbiAgICAgIGlmIChwcm9wVHlwZSAhPT0gJ29iamVjdCcpIHtcbiAgICAgICAgcmV0dXJuIG5ldyBQcm9wVHlwZUVycm9yKCdJbnZhbGlkICcgKyBsb2NhdGlvbiArICcgYCcgKyBwcm9wRnVsbE5hbWUgKyAnYCBvZiB0eXBlIGAnICsgcHJvcFR5cGUgKyAnYCAnICsgKCdzdXBwbGllZCB0byBgJyArIGNvbXBvbmVudE5hbWUgKyAnYCwgZXhwZWN0ZWQgYG9iamVjdGAuJykpO1xuICAgICAgfVxuICAgICAgZm9yICh2YXIga2V5IGluIHNoYXBlVHlwZXMpIHtcbiAgICAgICAgdmFyIGNoZWNrZXIgPSBzaGFwZVR5cGVzW2tleV07XG4gICAgICAgIGlmICh0eXBlb2YgY2hlY2tlciAhPT0gJ2Z1bmN0aW9uJykge1xuICAgICAgICAgIHJldHVybiBpbnZhbGlkVmFsaWRhdG9yRXJyb3IoY29tcG9uZW50TmFtZSwgbG9jYXRpb24sIHByb3BGdWxsTmFtZSwga2V5LCBnZXRQcmVjaXNlVHlwZShjaGVja2VyKSk7XG4gICAgICAgIH1cbiAgICAgICAgdmFyIGVycm9yID0gY2hlY2tlcihwcm9wVmFsdWUsIGtleSwgY29tcG9uZW50TmFtZSwgbG9jYXRpb24sIHByb3BGdWxsTmFtZSArICcuJyArIGtleSwgUmVhY3RQcm9wVHlwZXNTZWNyZXQpO1xuICAgICAgICBpZiAoZXJyb3IpIHtcbiAgICAgICAgICByZXR1cm4gZXJyb3I7XG4gICAgICAgIH1cbiAgICAgIH1cbiAgICAgIHJldHVybiBudWxsO1xuICAgIH1cbiAgICByZXR1cm4gY3JlYXRlQ2hhaW5hYmxlVHlwZUNoZWNrZXIodmFsaWRhdGUpO1xuICB9XG5cbiAgZnVuY3Rpb24gY3JlYXRlU3RyaWN0U2hhcGVUeXBlQ2hlY2tlcihzaGFwZVR5cGVzKSB7XG4gICAgZnVuY3Rpb24gdmFsaWRhdGUocHJvcHMsIHByb3BOYW1lLCBjb21wb25lbnROYW1lLCBsb2NhdGlvbiwgcHJvcEZ1bGxOYW1lKSB7XG4gICAgICB2YXIgcHJvcFZhbHVlID0gcHJvcHNbcHJvcE5hbWVdO1xuICAgICAgdmFyIHByb3BUeXBlID0gZ2V0UHJvcFR5cGUocHJvcFZhbHVlKTtcbiAgICAgIGlmIChwcm9wVHlwZSAhPT0gJ29iamVjdCcpIHtcbiAgICAgICAgcmV0dXJuIG5ldyBQcm9wVHlwZUVycm9yKCdJbnZhbGlkICcgKyBsb2NhdGlvbiArICcgYCcgKyBwcm9wRnVsbE5hbWUgKyAnYCBvZiB0eXBlIGAnICsgcHJvcFR5cGUgKyAnYCAnICsgKCdzdXBwbGllZCB0byBgJyArIGNvbXBvbmVudE5hbWUgKyAnYCwgZXhwZWN0ZWQgYG9iamVjdGAuJykpO1xuICAgICAgfVxuICAgICAgLy8gV2UgbmVlZCB0byBjaGVjayBhbGwga2V5cyBpbiBjYXNlIHNvbWUgYXJlIHJlcXVpcmVkIGJ1dCBtaXNzaW5nIGZyb20gcHJvcHMuXG4gICAgICB2YXIgYWxsS2V5cyA9IGFzc2lnbih7fSwgcHJvcHNbcHJvcE5hbWVdLCBzaGFwZVR5cGVzKTtcbiAgICAgIGZvciAodmFyIGtleSBpbiBhbGxLZXlzKSB7XG4gICAgICAgIHZhciBjaGVja2VyID0gc2hhcGVUeXBlc1trZXldO1xuICAgICAgICBpZiAoaGFzKHNoYXBlVHlwZXMsIGtleSkgJiYgdHlwZW9mIGNoZWNrZXIgIT09ICdmdW5jdGlvbicpIHtcbiAgICAgICAgICByZXR1cm4gaW52YWxpZFZhbGlkYXRvckVycm9yKGNvbXBvbmVudE5hbWUsIGxvY2F0aW9uLCBwcm9wRnVsbE5hbWUsIGtleSwgZ2V0UHJlY2lzZVR5cGUoY2hlY2tlcikpO1xuICAgICAgICB9XG4gICAgICAgIGlmICghY2hlY2tlcikge1xuICAgICAgICAgIHJldHVybiBuZXcgUHJvcFR5cGVFcnJvcihcbiAgICAgICAgICAgICdJbnZhbGlkICcgKyBsb2NhdGlvbiArICcgYCcgKyBwcm9wRnVsbE5hbWUgKyAnYCBrZXkgYCcgKyBrZXkgKyAnYCBzdXBwbGllZCB0byBgJyArIGNvbXBvbmVudE5hbWUgKyAnYC4nICtcbiAgICAgICAgICAgICdcXG5CYWQgb2JqZWN0OiAnICsgSlNPTi5zdHJpbmdpZnkocHJvcHNbcHJvcE5hbWVdLCBudWxsLCAnICAnKSArXG4gICAgICAgICAgICAnXFxuVmFsaWQga2V5czogJyArIEpTT04uc3RyaW5naWZ5KE9iamVjdC5rZXlzKHNoYXBlVHlwZXMpLCBudWxsLCAnICAnKVxuICAgICAgICAgICk7XG4gICAgICAgIH1cbiAgICAgICAgdmFyIGVycm9yID0gY2hlY2tlcihwcm9wVmFsdWUsIGtleSwgY29tcG9uZW50TmFtZSwgbG9jYXRpb24sIHByb3BGdWxsTmFtZSArICcuJyArIGtleSwgUmVhY3RQcm9wVHlwZXNTZWNyZXQpO1xuICAgICAgICBpZiAoZXJyb3IpIHtcbiAgICAgICAgICByZXR1cm4gZXJyb3I7XG4gICAgICAgIH1cbiAgICAgIH1cbiAgICAgIHJldHVybiBudWxsO1xuICAgIH1cblxuICAgIHJldHVybiBjcmVhdGVDaGFpbmFibGVUeXBlQ2hlY2tlcih2YWxpZGF0ZSk7XG4gIH1cblxuICBmdW5jdGlvbiBpc05vZGUocHJvcFZhbHVlKSB7XG4gICAgc3dpdGNoICh0eXBlb2YgcHJvcFZhbHVlKSB7XG4gICAgICBjYXNlICdudW1iZXInOlxuICAgICAgY2FzZSAnc3RyaW5nJzpcbiAgICAgIGNhc2UgJ3VuZGVmaW5lZCc6XG4gICAgICAgIHJldHVybiB0cnVlO1xuICAgICAgY2FzZSAnYm9vbGVhbic6XG4gICAgICAgIHJldHVybiAhcHJvcFZhbHVlO1xuICAgICAgY2FzZSAnb2JqZWN0JzpcbiAgICAgICAgaWYgKEFycmF5LmlzQXJyYXkocHJvcFZhbHVlKSkge1xuICAgICAgICAgIHJldHVybiBwcm9wVmFsdWUuZXZlcnkoaXNOb2RlKTtcbiAgICAgICAgfVxuICAgICAgICBpZiAocHJvcFZhbHVlID09PSBudWxsIHx8IGlzVmFsaWRFbGVtZW50KHByb3BWYWx1ZSkpIHtcbiAgICAgICAgICByZXR1cm4gdHJ1ZTtcbiAgICAgICAgfVxuXG4gICAgICAgIHZhciBpdGVyYXRvckZuID0gZ2V0SXRlcmF0b3JGbihwcm9wVmFsdWUpO1xuICAgICAgICBpZiAoaXRlcmF0b3JGbikge1xuICAgICAgICAgIHZhciBpdGVyYXRvciA9IGl0ZXJhdG9yRm4uY2FsbChwcm9wVmFsdWUpO1xuICAgICAgICAgIHZhciBzdGVwO1xuICAgICAgICAgIGlmIChpdGVyYXRvckZuICE9PSBwcm9wVmFsdWUuZW50cmllcykge1xuICAgICAgICAgICAgd2hpbGUgKCEoc3RlcCA9IGl0ZXJhdG9yLm5leHQoKSkuZG9uZSkge1xuICAgICAgICAgICAgICBpZiAoIWlzTm9kZShzdGVwLnZhbHVlKSkge1xuICAgICAgICAgICAgICAgIHJldHVybiBmYWxzZTtcbiAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgfVxuICAgICAgICAgIH0gZWxzZSB7XG4gICAgICAgICAgICAvLyBJdGVyYXRvciB3aWxsIHByb3ZpZGUgZW50cnkgW2ssdl0gdHVwbGVzIHJhdGhlciB0aGFuIHZhbHVlcy5cbiAgICAgICAgICAgIHdoaWxlICghKHN0ZXAgPSBpdGVyYXRvci5uZXh0KCkpLmRvbmUpIHtcbiAgICAgICAgICAgICAgdmFyIGVudHJ5ID0gc3RlcC52YWx1ZTtcbiAgICAgICAgICAgICAgaWYgKGVudHJ5KSB7XG4gICAgICAgICAgICAgICAgaWYgKCFpc05vZGUoZW50cnlbMV0pKSB7XG4gICAgICAgICAgICAgICAgICByZXR1cm4gZmFsc2U7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICB9XG4gICAgICAgICAgICB9XG4gICAgICAgICAgfVxuICAgICAgICB9IGVsc2Uge1xuICAgICAgICAgIHJldHVybiBmYWxzZTtcbiAgICAgICAgfVxuXG4gICAgICAgIHJldHVybiB0cnVlO1xuICAgICAgZGVmYXVsdDpcbiAgICAgICAgcmV0dXJuIGZhbHNlO1xuICAgIH1cbiAgfVxuXG4gIGZ1bmN0aW9uIGlzU3ltYm9sKHByb3BUeXBlLCBwcm9wVmFsdWUpIHtcbiAgICAvLyBOYXRpdmUgU3ltYm9sLlxuICAgIGlmIChwcm9wVHlwZSA9PT0gJ3N5bWJvbCcpIHtcbiAgICAgIHJldHVybiB0cnVlO1xuICAgIH1cblxuICAgIC8vIGZhbHN5IHZhbHVlIGNhbid0IGJlIGEgU3ltYm9sXG4gICAgaWYgKCFwcm9wVmFsdWUpIHtcbiAgICAgIHJldHVybiBmYWxzZTtcbiAgICB9XG5cbiAgICAvLyAxOS40LjMuNSBTeW1ib2wucHJvdG90eXBlW0BAdG9TdHJpbmdUYWddID09PSAnU3ltYm9sJ1xuICAgIGlmIChwcm9wVmFsdWVbJ0BAdG9TdHJpbmdUYWcnXSA9PT0gJ1N5bWJvbCcpIHtcbiAgICAgIHJldHVybiB0cnVlO1xuICAgIH1cblxuICAgIC8vIEZhbGxiYWNrIGZvciBub24tc3BlYyBjb21wbGlhbnQgU3ltYm9scyB3aGljaCBhcmUgcG9seWZpbGxlZC5cbiAgICBpZiAodHlwZW9mIFN5bWJvbCA9PT0gJ2Z1bmN0aW9uJyAmJiBwcm9wVmFsdWUgaW5zdGFuY2VvZiBTeW1ib2wpIHtcbiAgICAgIHJldHVybiB0cnVlO1xuICAgIH1cblxuICAgIHJldHVybiBmYWxzZTtcbiAgfVxuXG4gIC8vIEVxdWl2YWxlbnQgb2YgYHR5cGVvZmAgYnV0IHdpdGggc3BlY2lhbCBoYW5kbGluZyBmb3IgYXJyYXkgYW5kIHJlZ2V4cC5cbiAgZnVuY3Rpb24gZ2V0UHJvcFR5cGUocHJvcFZhbHVlKSB7XG4gICAgdmFyIHByb3BUeXBlID0gdHlwZW9mIHByb3BWYWx1ZTtcbiAgICBpZiAoQXJyYXkuaXNBcnJheShwcm9wVmFsdWUpKSB7XG4gICAgICByZXR1cm4gJ2FycmF5JztcbiAgICB9XG4gICAgaWYgKHByb3BWYWx1ZSBpbnN0YW5jZW9mIFJlZ0V4cCkge1xuICAgICAgLy8gT2xkIHdlYmtpdHMgKGF0IGxlYXN0IHVudGlsIEFuZHJvaWQgNC4wKSByZXR1cm4gJ2Z1bmN0aW9uJyByYXRoZXIgdGhhblxuICAgICAgLy8gJ29iamVjdCcgZm9yIHR5cGVvZiBhIFJlZ0V4cC4gV2UnbGwgbm9ybWFsaXplIHRoaXMgaGVyZSBzbyB0aGF0IC9ibGEvXG4gICAgICAvLyBwYXNzZXMgUHJvcFR5cGVzLm9iamVjdC5cbiAgICAgIHJldHVybiAnb2JqZWN0JztcbiAgICB9XG4gICAgaWYgKGlzU3ltYm9sKHByb3BUeXBlLCBwcm9wVmFsdWUpKSB7XG4gICAgICByZXR1cm4gJ3N5bWJvbCc7XG4gICAgfVxuICAgIHJldHVybiBwcm9wVHlwZTtcbiAgfVxuXG4gIC8vIFRoaXMgaGFuZGxlcyBtb3JlIHR5cGVzIHRoYW4gYGdldFByb3BUeXBlYC4gT25seSB1c2VkIGZvciBlcnJvciBtZXNzYWdlcy5cbiAgLy8gU2VlIGBjcmVhdGVQcmltaXRpdmVUeXBlQ2hlY2tlcmAuXG4gIGZ1bmN0aW9uIGdldFByZWNpc2VUeXBlKHByb3BWYWx1ZSkge1xuICAgIGlmICh0eXBlb2YgcHJvcFZhbHVlID09PSAndW5kZWZpbmVkJyB8fCBwcm9wVmFsdWUgPT09IG51bGwpIHtcbiAgICAgIHJldHVybiAnJyArIHByb3BWYWx1ZTtcbiAgICB9XG4gICAgdmFyIHByb3BUeXBlID0gZ2V0UHJvcFR5cGUocHJvcFZhbHVlKTtcbiAgICBpZiAocHJvcFR5cGUgPT09ICdvYmplY3QnKSB7XG4gICAgICBpZiAocHJvcFZhbHVlIGluc3RhbmNlb2YgRGF0ZSkge1xuICAgICAgICByZXR1cm4gJ2RhdGUnO1xuICAgICAgfSBlbHNlIGlmIChwcm9wVmFsdWUgaW5zdGFuY2VvZiBSZWdFeHApIHtcbiAgICAgICAgcmV0dXJuICdyZWdleHAnO1xuICAgICAgfVxuICAgIH1cbiAgICByZXR1cm4gcHJvcFR5cGU7XG4gIH1cblxuICAvLyBSZXR1cm5zIGEgc3RyaW5nIHRoYXQgaXMgcG9zdGZpeGVkIHRvIGEgd2FybmluZyBhYm91dCBhbiBpbnZhbGlkIHR5cGUuXG4gIC8vIEZvciBleGFtcGxlLCBcInVuZGVmaW5lZFwiIG9yIFwib2YgdHlwZSBhcnJheVwiXG4gIGZ1bmN0aW9uIGdldFBvc3RmaXhGb3JUeXBlV2FybmluZyh2YWx1ZSkge1xuICAgIHZhciB0eXBlID0gZ2V0UHJlY2lzZVR5cGUodmFsdWUpO1xuICAgIHN3aXRjaCAodHlwZSkge1xuICAgICAgY2FzZSAnYXJyYXknOlxuICAgICAgY2FzZSAnb2JqZWN0JzpcbiAgICAgICAgcmV0dXJuICdhbiAnICsgdHlwZTtcbiAgICAgIGNhc2UgJ2Jvb2xlYW4nOlxuICAgICAgY2FzZSAnZGF0ZSc6XG4gICAgICBjYXNlICdyZWdleHAnOlxuICAgICAgICByZXR1cm4gJ2EgJyArIHR5cGU7XG4gICAgICBkZWZhdWx0OlxuICAgICAgICByZXR1cm4gdHlwZTtcbiAgICB9XG4gIH1cblxuICAvLyBSZXR1cm5zIGNsYXNzIG5hbWUgb2YgdGhlIG9iamVjdCwgaWYgYW55LlxuICBmdW5jdGlvbiBnZXRDbGFzc05hbWUocHJvcFZhbHVlKSB7XG4gICAgaWYgKCFwcm9wVmFsdWUuY29uc3RydWN0b3IgfHwgIXByb3BWYWx1ZS5jb25zdHJ1Y3Rvci5uYW1lKSB7XG4gICAgICByZXR1cm4gQU5PTllNT1VTO1xuICAgIH1cbiAgICByZXR1cm4gcHJvcFZhbHVlLmNvbnN0cnVjdG9yLm5hbWU7XG4gIH1cblxuICBSZWFjdFByb3BUeXBlcy5jaGVja1Byb3BUeXBlcyA9IGNoZWNrUHJvcFR5cGVzO1xuICBSZWFjdFByb3BUeXBlcy5yZXNldFdhcm5pbmdDYWNoZSA9IGNoZWNrUHJvcFR5cGVzLnJlc2V0V2FybmluZ0NhY2hlO1xuICBSZWFjdFByb3BUeXBlcy5Qcm9wVHlwZXMgPSBSZWFjdFByb3BUeXBlcztcblxuICByZXR1cm4gUmVhY3RQcm9wVHlwZXM7XG59O1xuIiwiLyoqXG4gKiBDb3B5cmlnaHQgKGMpIDIwMTMtcHJlc2VudCwgRmFjZWJvb2ssIEluYy5cbiAqXG4gKiBUaGlzIHNvdXJjZSBjb2RlIGlzIGxpY2Vuc2VkIHVuZGVyIHRoZSBNSVQgbGljZW5zZSBmb3VuZCBpbiB0aGVcbiAqIExJQ0VOU0UgZmlsZSBpbiB0aGUgcm9vdCBkaXJlY3Rvcnkgb2YgdGhpcyBzb3VyY2UgdHJlZS5cbiAqL1xuXG5pZiAocHJvY2Vzcy5lbnYuTk9ERV9FTlYgIT09ICdwcm9kdWN0aW9uJykge1xuICB2YXIgUmVhY3RJcyA9IHJlcXVpcmUoJ3JlYWN0LWlzJyk7XG5cbiAgLy8gQnkgZXhwbGljaXRseSB1c2luZyBgcHJvcC10eXBlc2AgeW91IGFyZSBvcHRpbmcgaW50byBuZXcgZGV2ZWxvcG1lbnQgYmVoYXZpb3IuXG4gIC8vIGh0dHA6Ly9mYi5tZS9wcm9wLXR5cGVzLWluLXByb2RcbiAgdmFyIHRocm93T25EaXJlY3RBY2Nlc3MgPSB0cnVlO1xuICBtb2R1bGUuZXhwb3J0cyA9IHJlcXVpcmUoJy4vZmFjdG9yeVdpdGhUeXBlQ2hlY2tlcnMnKShSZWFjdElzLmlzRWxlbWVudCwgdGhyb3dPbkRpcmVjdEFjY2Vzcyk7XG59IGVsc2Uge1xuICAvLyBCeSBleHBsaWNpdGx5IHVzaW5nIGBwcm9wLXR5cGVzYCB5b3UgYXJlIG9wdGluZyBpbnRvIG5ldyBwcm9kdWN0aW9uIGJlaGF2aW9yLlxuICAvLyBodHRwOi8vZmIubWUvcHJvcC10eXBlcy1pbi1wcm9kXG4gIG1vZHVsZS5leHBvcnRzID0gcmVxdWlyZSgnLi9mYWN0b3J5V2l0aFRocm93aW5nU2hpbXMnKSgpO1xufVxuIiwiXG5tb2R1bGUuZXhwb3J0cyA9IGZ1bmN0aW9uIGNoYWluKCl7XG4gIHZhciBsZW4gPSBhcmd1bWVudHMubGVuZ3RoXG4gIHZhciBhcmdzID0gW107XG5cbiAgZm9yICh2YXIgaSA9IDA7IGkgPCBsZW47IGkrKylcbiAgICBhcmdzW2ldID0gYXJndW1lbnRzW2ldXG5cbiAgYXJncyA9IGFyZ3MuZmlsdGVyKGZ1bmN0aW9uKGZuKXsgcmV0dXJuIGZuICE9IG51bGwgfSlcblxuICBpZiAoYXJncy5sZW5ndGggPT09IDApIHJldHVybiB1bmRlZmluZWRcbiAgaWYgKGFyZ3MubGVuZ3RoID09PSAxKSByZXR1cm4gYXJnc1swXVxuXG4gIHJldHVybiBhcmdzLnJlZHVjZShmdW5jdGlvbihjdXJyZW50LCBuZXh0KXtcbiAgICByZXR1cm4gZnVuY3Rpb24gY2hhaW5lZEZ1bmN0aW9uKCkge1xuICAgICAgY3VycmVudC5hcHBseSh0aGlzLCBhcmd1bWVudHMpO1xuICAgICAgbmV4dC5hcHBseSh0aGlzLCBhcmd1bWVudHMpO1xuICAgIH07XG4gIH0pXG59XG4iLCIvKipcbiAqIENvcHlyaWdodCAyMDE0LTIwMTUsIEZhY2Vib29rLCBJbmMuXG4gKiBBbGwgcmlnaHRzIHJlc2VydmVkLlxuICpcbiAqIFRoaXMgc291cmNlIGNvZGUgaXMgbGljZW5zZWQgdW5kZXIgdGhlIEJTRC1zdHlsZSBsaWNlbnNlIGZvdW5kIGluIHRoZVxuICogTElDRU5TRSBmaWxlIGluIHRoZSByb290IGRpcmVjdG9yeSBvZiB0aGlzIHNvdXJjZSB0cmVlLiBBbiBhZGRpdGlvbmFsIGdyYW50XG4gKiBvZiBwYXRlbnQgcmlnaHRzIGNhbiBiZSBmb3VuZCBpbiB0aGUgUEFURU5UUyBmaWxlIGluIHRoZSBzYW1lIGRpcmVjdG9yeS5cbiAqL1xuXG4ndXNlIHN0cmljdCc7XG5cbi8qKlxuICogU2ltaWxhciB0byBpbnZhcmlhbnQgYnV0IG9ubHkgbG9ncyBhIHdhcm5pbmcgaWYgdGhlIGNvbmRpdGlvbiBpcyBub3QgbWV0LlxuICogVGhpcyBjYW4gYmUgdXNlZCB0byBsb2cgaXNzdWVzIGluIGRldmVsb3BtZW50IGVudmlyb25tZW50cyBpbiBjcml0aWNhbFxuICogcGF0aHMuIFJlbW92aW5nIHRoZSBsb2dnaW5nIGNvZGUgZm9yIHByb2R1Y3Rpb24gZW52aXJvbm1lbnRzIHdpbGwga2VlcCB0aGVcbiAqIHNhbWUgbG9naWMgYW5kIGZvbGxvdyB0aGUgc2FtZSBjb2RlIHBhdGhzLlxuICovXG5cbnZhciB3YXJuaW5nID0gZnVuY3Rpb24oKSB7fTtcblxuaWYgKHByb2Nlc3MuZW52Lk5PREVfRU5WICE9PSAncHJvZHVjdGlvbicpIHtcbiAgd2FybmluZyA9IGZ1bmN0aW9uKGNvbmRpdGlvbiwgZm9ybWF0LCBhcmdzKSB7XG4gICAgdmFyIGxlbiA9IGFyZ3VtZW50cy5sZW5ndGg7XG4gICAgYXJncyA9IG5ldyBBcnJheShsZW4gPiAyID8gbGVuIC0gMiA6IDApO1xuICAgIGZvciAodmFyIGtleSA9IDI7IGtleSA8IGxlbjsga2V5KyspIHtcbiAgICAgIGFyZ3Nba2V5IC0gMl0gPSBhcmd1bWVudHNba2V5XTtcbiAgICB9XG4gICAgaWYgKGZvcm1hdCA9PT0gdW5kZWZpbmVkKSB7XG4gICAgICB0aHJvdyBuZXcgRXJyb3IoXG4gICAgICAgICdgd2FybmluZyhjb25kaXRpb24sIGZvcm1hdCwgLi4uYXJncylgIHJlcXVpcmVzIGEgd2FybmluZyAnICtcbiAgICAgICAgJ21lc3NhZ2UgYXJndW1lbnQnXG4gICAgICApO1xuICAgIH1cblxuICAgIGlmIChmb3JtYXQubGVuZ3RoIDwgMTAgfHwgKC9eW3NcXFddKiQvKS50ZXN0KGZvcm1hdCkpIHtcbiAgICAgIHRocm93IG5ldyBFcnJvcihcbiAgICAgICAgJ1RoZSB3YXJuaW5nIGZvcm1hdCBzaG91bGQgYmUgYWJsZSB0byB1bmlxdWVseSBpZGVudGlmeSB0aGlzICcgK1xuICAgICAgICAnd2FybmluZy4gUGxlYXNlLCB1c2UgYSBtb3JlIGRlc2NyaXB0aXZlIGZvcm1hdCB0aGFuOiAnICsgZm9ybWF0XG4gICAgICApO1xuICAgIH1cblxuICAgIGlmICghY29uZGl0aW9uKSB7XG4gICAgICB2YXIgYXJnSW5kZXggPSAwO1xuICAgICAgdmFyIG1lc3NhZ2UgPSAnV2FybmluZzogJyArXG4gICAgICAgIGZvcm1hdC5yZXBsYWNlKC8lcy9nLCBmdW5jdGlvbigpIHtcbiAgICAgICAgICByZXR1cm4gYXJnc1thcmdJbmRleCsrXTtcbiAgICAgICAgfSk7XG4gICAgICBpZiAodHlwZW9mIGNvbnNvbGUgIT09ICd1bmRlZmluZWQnKSB7XG4gICAgICAgIGNvbnNvbGUuZXJyb3IobWVzc2FnZSk7XG4gICAgICB9XG4gICAgICB0cnkge1xuICAgICAgICAvLyBUaGlzIGVycm9yIHdhcyB0aHJvd24gYXMgYSBjb252ZW5pZW5jZSBzbyB0aGF0IHlvdSBjYW4gdXNlIHRoaXMgc3RhY2tcbiAgICAgICAgLy8gdG8gZmluZCB0aGUgY2FsbHNpdGUgdGhhdCBjYXVzZWQgdGhpcyB3YXJuaW5nIHRvIGZpcmUuXG4gICAgICAgIHRocm93IG5ldyBFcnJvcihtZXNzYWdlKTtcbiAgICAgIH0gY2F0Y2goeCkge31cbiAgICB9XG4gIH07XG59XG5cbm1vZHVsZS5leHBvcnRzID0gd2FybmluZztcbiIsIi8qKlxuICogQ29weXJpZ2h0IChjKSAyMDEzLXByZXNlbnQsIEZhY2Vib29rLCBJbmMuXG4gKlxuICogVGhpcyBzb3VyY2UgY29kZSBpcyBsaWNlbnNlZCB1bmRlciB0aGUgTUlUIGxpY2Vuc2UgZm91bmQgaW4gdGhlXG4gKiBMSUNFTlNFIGZpbGUgaW4gdGhlIHJvb3QgZGlyZWN0b3J5IG9mIHRoaXMgc291cmNlIHRyZWUuXG4gKi9cblxuZnVuY3Rpb24gY29tcG9uZW50V2lsbE1vdW50KCkge1xuICAvLyBDYWxsIHRoaXMuY29uc3RydWN0b3IuZ0RTRlAgdG8gc3VwcG9ydCBzdWItY2xhc3Nlcy5cbiAgdmFyIHN0YXRlID0gdGhpcy5jb25zdHJ1Y3Rvci5nZXREZXJpdmVkU3RhdGVGcm9tUHJvcHModGhpcy5wcm9wcywgdGhpcy5zdGF0ZSk7XG4gIGlmIChzdGF0ZSAhPT0gbnVsbCAmJiBzdGF0ZSAhPT0gdW5kZWZpbmVkKSB7XG4gICAgdGhpcy5zZXRTdGF0ZShzdGF0ZSk7XG4gIH1cbn1cblxuZnVuY3Rpb24gY29tcG9uZW50V2lsbFJlY2VpdmVQcm9wcyhuZXh0UHJvcHMpIHtcbiAgLy8gQ2FsbCB0aGlzLmNvbnN0cnVjdG9yLmdEU0ZQIHRvIHN1cHBvcnQgc3ViLWNsYXNzZXMuXG4gIC8vIFVzZSB0aGUgc2V0U3RhdGUoKSB1cGRhdGVyIHRvIGVuc3VyZSBzdGF0ZSBpc24ndCBzdGFsZSBpbiBjZXJ0YWluIGVkZ2UgY2FzZXMuXG4gIGZ1bmN0aW9uIHVwZGF0ZXIocHJldlN0YXRlKSB7XG4gICAgdmFyIHN0YXRlID0gdGhpcy5jb25zdHJ1Y3Rvci5nZXREZXJpdmVkU3RhdGVGcm9tUHJvcHMobmV4dFByb3BzLCBwcmV2U3RhdGUpO1xuICAgIHJldHVybiBzdGF0ZSAhPT0gbnVsbCAmJiBzdGF0ZSAhPT0gdW5kZWZpbmVkID8gc3RhdGUgOiBudWxsO1xuICB9XG4gIC8vIEJpbmRpbmcgXCJ0aGlzXCIgaXMgaW1wb3J0YW50IGZvciBzaGFsbG93IHJlbmRlcmVyIHN1cHBvcnQuXG4gIHRoaXMuc2V0U3RhdGUodXBkYXRlci5iaW5kKHRoaXMpKTtcbn1cblxuZnVuY3Rpb24gY29tcG9uZW50V2lsbFVwZGF0ZShuZXh0UHJvcHMsIG5leHRTdGF0ZSkge1xuICB0cnkge1xuICAgIHZhciBwcmV2UHJvcHMgPSB0aGlzLnByb3BzO1xuICAgIHZhciBwcmV2U3RhdGUgPSB0aGlzLnN0YXRlO1xuICAgIHRoaXMucHJvcHMgPSBuZXh0UHJvcHM7XG4gICAgdGhpcy5zdGF0ZSA9IG5leHRTdGF0ZTtcbiAgICB0aGlzLl9fcmVhY3RJbnRlcm5hbFNuYXBzaG90RmxhZyA9IHRydWU7XG4gICAgdGhpcy5fX3JlYWN0SW50ZXJuYWxTbmFwc2hvdCA9IHRoaXMuZ2V0U25hcHNob3RCZWZvcmVVcGRhdGUoXG4gICAgICBwcmV2UHJvcHMsXG4gICAgICBwcmV2U3RhdGVcbiAgICApO1xuICB9IGZpbmFsbHkge1xuICAgIHRoaXMucHJvcHMgPSBwcmV2UHJvcHM7XG4gICAgdGhpcy5zdGF0ZSA9IHByZXZTdGF0ZTtcbiAgfVxufVxuXG4vLyBSZWFjdCBtYXkgd2FybiBhYm91dCBjV00vY1dSUC9jV1UgbWV0aG9kcyBiZWluZyBkZXByZWNhdGVkLlxuLy8gQWRkIGEgZmxhZyB0byBzdXBwcmVzcyB0aGVzZSB3YXJuaW5ncyBmb3IgdGhpcyBzcGVjaWFsIGNhc2UuXG5jb21wb25lbnRXaWxsTW91bnQuX19zdXBwcmVzc0RlcHJlY2F0aW9uV2FybmluZyA9IHRydWU7XG5jb21wb25lbnRXaWxsUmVjZWl2ZVByb3BzLl9fc3VwcHJlc3NEZXByZWNhdGlvbldhcm5pbmcgPSB0cnVlO1xuY29tcG9uZW50V2lsbFVwZGF0ZS5fX3N1cHByZXNzRGVwcmVjYXRpb25XYXJuaW5nID0gdHJ1ZTtcblxuZnVuY3Rpb24gcG9seWZpbGwoQ29tcG9uZW50KSB7XG4gIHZhciBwcm90b3R5cGUgPSBDb21wb25lbnQucHJvdG90eXBlO1xuXG4gIGlmICghcHJvdG90eXBlIHx8ICFwcm90b3R5cGUuaXNSZWFjdENvbXBvbmVudCkge1xuICAgIHRocm93IG5ldyBFcnJvcignQ2FuIG9ubHkgcG9seWZpbGwgY2xhc3MgY29tcG9uZW50cycpO1xuICB9XG5cbiAgaWYgKFxuICAgIHR5cGVvZiBDb21wb25lbnQuZ2V0RGVyaXZlZFN0YXRlRnJvbVByb3BzICE9PSAnZnVuY3Rpb24nICYmXG4gICAgdHlwZW9mIHByb3RvdHlwZS5nZXRTbmFwc2hvdEJlZm9yZVVwZGF0ZSAhPT0gJ2Z1bmN0aW9uJ1xuICApIHtcbiAgICByZXR1cm4gQ29tcG9uZW50O1xuICB9XG5cbiAgLy8gSWYgbmV3IGNvbXBvbmVudCBBUElzIGFyZSBkZWZpbmVkLCBcInVuc2FmZVwiIGxpZmVjeWNsZXMgd29uJ3QgYmUgY2FsbGVkLlxuICAvLyBFcnJvciBpZiBhbnkgb2YgdGhlc2UgbGlmZWN5Y2xlcyBhcmUgcHJlc2VudCxcbiAgLy8gQmVjYXVzZSB0aGV5IHdvdWxkIHdvcmsgZGlmZmVyZW50bHkgYmV0d2VlbiBvbGRlciBhbmQgbmV3ZXIgKDE2LjMrKSB2ZXJzaW9ucyBvZiBSZWFjdC5cbiAgdmFyIGZvdW5kV2lsbE1vdW50TmFtZSA9IG51bGw7XG4gIHZhciBmb3VuZFdpbGxSZWNlaXZlUHJvcHNOYW1lID0gbnVsbDtcbiAgdmFyIGZvdW5kV2lsbFVwZGF0ZU5hbWUgPSBudWxsO1xuICBpZiAodHlwZW9mIHByb3RvdHlwZS5jb21wb25lbnRXaWxsTW91bnQgPT09ICdmdW5jdGlvbicpIHtcbiAgICBmb3VuZFdpbGxNb3VudE5hbWUgPSAnY29tcG9uZW50V2lsbE1vdW50JztcbiAgfSBlbHNlIGlmICh0eXBlb2YgcHJvdG90eXBlLlVOU0FGRV9jb21wb25lbnRXaWxsTW91bnQgPT09ICdmdW5jdGlvbicpIHtcbiAgICBmb3VuZFdpbGxNb3VudE5hbWUgPSAnVU5TQUZFX2NvbXBvbmVudFdpbGxNb3VudCc7XG4gIH1cbiAgaWYgKHR5cGVvZiBwcm90b3R5cGUuY29tcG9uZW50V2lsbFJlY2VpdmVQcm9wcyA9PT0gJ2Z1bmN0aW9uJykge1xuICAgIGZvdW5kV2lsbFJlY2VpdmVQcm9wc05hbWUgPSAnY29tcG9uZW50V2lsbFJlY2VpdmVQcm9wcyc7XG4gIH0gZWxzZSBpZiAodHlwZW9mIHByb3RvdHlwZS5VTlNBRkVfY29tcG9uZW50V2lsbFJlY2VpdmVQcm9wcyA9PT0gJ2Z1bmN0aW9uJykge1xuICAgIGZvdW5kV2lsbFJlY2VpdmVQcm9wc05hbWUgPSAnVU5TQUZFX2NvbXBvbmVudFdpbGxSZWNlaXZlUHJvcHMnO1xuICB9XG4gIGlmICh0eXBlb2YgcHJvdG90eXBlLmNvbXBvbmVudFdpbGxVcGRhdGUgPT09ICdmdW5jdGlvbicpIHtcbiAgICBmb3VuZFdpbGxVcGRhdGVOYW1lID0gJ2NvbXBvbmVudFdpbGxVcGRhdGUnO1xuICB9IGVsc2UgaWYgKHR5cGVvZiBwcm90b3R5cGUuVU5TQUZFX2NvbXBvbmVudFdpbGxVcGRhdGUgPT09ICdmdW5jdGlvbicpIHtcbiAgICBmb3VuZFdpbGxVcGRhdGVOYW1lID0gJ1VOU0FGRV9jb21wb25lbnRXaWxsVXBkYXRlJztcbiAgfVxuICBpZiAoXG4gICAgZm91bmRXaWxsTW91bnROYW1lICE9PSBudWxsIHx8XG4gICAgZm91bmRXaWxsUmVjZWl2ZVByb3BzTmFtZSAhPT0gbnVsbCB8fFxuICAgIGZvdW5kV2lsbFVwZGF0ZU5hbWUgIT09IG51bGxcbiAgKSB7XG4gICAgdmFyIGNvbXBvbmVudE5hbWUgPSBDb21wb25lbnQuZGlzcGxheU5hbWUgfHwgQ29tcG9uZW50Lm5hbWU7XG4gICAgdmFyIG5ld0FwaU5hbWUgPVxuICAgICAgdHlwZW9mIENvbXBvbmVudC5nZXREZXJpdmVkU3RhdGVGcm9tUHJvcHMgPT09ICdmdW5jdGlvbidcbiAgICAgICAgPyAnZ2V0RGVyaXZlZFN0YXRlRnJvbVByb3BzKCknXG4gICAgICAgIDogJ2dldFNuYXBzaG90QmVmb3JlVXBkYXRlKCknO1xuXG4gICAgdGhyb3cgRXJyb3IoXG4gICAgICAnVW5zYWZlIGxlZ2FjeSBsaWZlY3ljbGVzIHdpbGwgbm90IGJlIGNhbGxlZCBmb3IgY29tcG9uZW50cyB1c2luZyBuZXcgY29tcG9uZW50IEFQSXMuXFxuXFxuJyArXG4gICAgICAgIGNvbXBvbmVudE5hbWUgK1xuICAgICAgICAnIHVzZXMgJyArXG4gICAgICAgIG5ld0FwaU5hbWUgK1xuICAgICAgICAnIGJ1dCBhbHNvIGNvbnRhaW5zIHRoZSBmb2xsb3dpbmcgbGVnYWN5IGxpZmVjeWNsZXM6JyArXG4gICAgICAgIChmb3VuZFdpbGxNb3VudE5hbWUgIT09IG51bGwgPyAnXFxuICAnICsgZm91bmRXaWxsTW91bnROYW1lIDogJycpICtcbiAgICAgICAgKGZvdW5kV2lsbFJlY2VpdmVQcm9wc05hbWUgIT09IG51bGxcbiAgICAgICAgICA/ICdcXG4gICcgKyBmb3VuZFdpbGxSZWNlaXZlUHJvcHNOYW1lXG4gICAgICAgICAgOiAnJykgK1xuICAgICAgICAoZm91bmRXaWxsVXBkYXRlTmFtZSAhPT0gbnVsbCA/ICdcXG4gICcgKyBmb3VuZFdpbGxVcGRhdGVOYW1lIDogJycpICtcbiAgICAgICAgJ1xcblxcblRoZSBhYm92ZSBsaWZlY3ljbGVzIHNob3VsZCBiZSByZW1vdmVkLiBMZWFybiBtb3JlIGFib3V0IHRoaXMgd2FybmluZyBoZXJlOlxcbicgK1xuICAgICAgICAnaHR0cHM6Ly9mYi5tZS9yZWFjdC1hc3luYy1jb21wb25lbnQtbGlmZWN5Y2xlLWhvb2tzJ1xuICAgICk7XG4gIH1cblxuICAvLyBSZWFjdCA8PSAxNi4yIGRvZXMgbm90IHN1cHBvcnQgc3RhdGljIGdldERlcml2ZWRTdGF0ZUZyb21Qcm9wcy5cbiAgLy8gQXMgYSB3b3JrYXJvdW5kLCB1c2UgY1dNIGFuZCBjV1JQIHRvIGludm9rZSB0aGUgbmV3IHN0YXRpYyBsaWZlY3ljbGUuXG4gIC8vIE5ld2VyIHZlcnNpb25zIG9mIFJlYWN0IHdpbGwgaWdub3JlIHRoZXNlIGxpZmVjeWNsZXMgaWYgZ0RTRlAgZXhpc3RzLlxuICBpZiAodHlwZW9mIENvbXBvbmVudC5nZXREZXJpdmVkU3RhdGVGcm9tUHJvcHMgPT09ICdmdW5jdGlvbicpIHtcbiAgICBwcm90b3R5cGUuY29tcG9uZW50V2lsbE1vdW50ID0gY29tcG9uZW50V2lsbE1vdW50O1xuICAgIHByb3RvdHlwZS5jb21wb25lbnRXaWxsUmVjZWl2ZVByb3BzID0gY29tcG9uZW50V2lsbFJlY2VpdmVQcm9wcztcbiAgfVxuXG4gIC8vIFJlYWN0IDw9IDE2LjIgZG9lcyBub3Qgc3VwcG9ydCBnZXRTbmFwc2hvdEJlZm9yZVVwZGF0ZS5cbiAgLy8gQXMgYSB3b3JrYXJvdW5kLCB1c2UgY1dVIHRvIGludm9rZSB0aGUgbmV3IGxpZmVjeWNsZS5cbiAgLy8gTmV3ZXIgdmVyc2lvbnMgb2YgUmVhY3Qgd2lsbCBpZ25vcmUgdGhhdCBsaWZlY3ljbGUgaWYgZ1NCVSBleGlzdHMuXG4gIGlmICh0eXBlb2YgcHJvdG90eXBlLmdldFNuYXBzaG90QmVmb3JlVXBkYXRlID09PSAnZnVuY3Rpb24nKSB7XG4gICAgaWYgKHR5cGVvZiBwcm90b3R5cGUuY29tcG9uZW50RGlkVXBkYXRlICE9PSAnZnVuY3Rpb24nKSB7XG4gICAgICB0aHJvdyBuZXcgRXJyb3IoXG4gICAgICAgICdDYW5ub3QgcG9seWZpbGwgZ2V0U25hcHNob3RCZWZvcmVVcGRhdGUoKSBmb3IgY29tcG9uZW50cyB0aGF0IGRvIG5vdCBkZWZpbmUgY29tcG9uZW50RGlkVXBkYXRlKCkgb24gdGhlIHByb3RvdHlwZSdcbiAgICAgICk7XG4gICAgfVxuXG4gICAgcHJvdG90eXBlLmNvbXBvbmVudFdpbGxVcGRhdGUgPSBjb21wb25lbnRXaWxsVXBkYXRlO1xuXG4gICAgdmFyIGNvbXBvbmVudERpZFVwZGF0ZSA9IHByb3RvdHlwZS5jb21wb25lbnREaWRVcGRhdGU7XG5cbiAgICBwcm90b3R5cGUuY29tcG9uZW50RGlkVXBkYXRlID0gZnVuY3Rpb24gY29tcG9uZW50RGlkVXBkYXRlUG9seWZpbGwoXG4gICAgICBwcmV2UHJvcHMsXG4gICAgICBwcmV2U3RhdGUsXG4gICAgICBtYXliZVNuYXBzaG90XG4gICAgKSB7XG4gICAgICAvLyAxNi4zKyB3aWxsIG5vdCBleGVjdXRlIG91ciB3aWxsLXVwZGF0ZSBtZXRob2Q7XG4gICAgICAvLyBJdCB3aWxsIHBhc3MgYSBzbmFwc2hvdCB2YWx1ZSB0byBkaWQtdXBkYXRlIHRob3VnaC5cbiAgICAgIC8vIE9sZGVyIHZlcnNpb25zIHdpbGwgcmVxdWlyZSBvdXIgcG9seWZpbGxlZCB3aWxsLXVwZGF0ZSB2YWx1ZS5cbiAgICAgIC8vIFdlIG5lZWQgdG8gaGFuZGxlIGJvdGggY2FzZXMsIGJ1dCBjYW4ndCBqdXN0IGNoZWNrIGZvciB0aGUgcHJlc2VuY2Ugb2YgXCJtYXliZVNuYXBzaG90XCIsXG4gICAgICAvLyBCZWNhdXNlIGZvciA8PSAxNS54IHZlcnNpb25zIHRoaXMgbWlnaHQgYmUgYSBcInByZXZDb250ZXh0XCIgb2JqZWN0LlxuICAgICAgLy8gV2UgYWxzbyBjYW4ndCBqdXN0IGNoZWNrIFwiX19yZWFjdEludGVybmFsU25hcHNob3RcIixcbiAgICAgIC8vIEJlY2F1c2UgZ2V0LXNuYXBzaG90IG1pZ2h0IHJldHVybiBhIGZhbHN5IHZhbHVlLlxuICAgICAgLy8gU28gY2hlY2sgZm9yIHRoZSBleHBsaWNpdCBfX3JlYWN0SW50ZXJuYWxTbmFwc2hvdEZsYWcgZmxhZyB0byBkZXRlcm1pbmUgYmVoYXZpb3IuXG4gICAgICB2YXIgc25hcHNob3QgPSB0aGlzLl9fcmVhY3RJbnRlcm5hbFNuYXBzaG90RmxhZ1xuICAgICAgICA/IHRoaXMuX19yZWFjdEludGVybmFsU25hcHNob3RcbiAgICAgICAgOiBtYXliZVNuYXBzaG90O1xuXG4gICAgICBjb21wb25lbnREaWRVcGRhdGUuY2FsbCh0aGlzLCBwcmV2UHJvcHMsIHByZXZTdGF0ZSwgc25hcHNob3QpO1xuICAgIH07XG4gIH1cblxuICByZXR1cm4gQ29tcG9uZW50O1xufVxuXG5leHBvcnQgeyBwb2x5ZmlsbCB9O1xuIiwiJ3VzZSBzdHJpY3QnO1xuXG5leHBvcnRzLl9fZXNNb2R1bGUgPSB0cnVlO1xuZXhwb3J0cy5nZXRDaGlsZE1hcHBpbmcgPSBnZXRDaGlsZE1hcHBpbmc7XG5leHBvcnRzLm1lcmdlQ2hpbGRNYXBwaW5ncyA9IG1lcmdlQ2hpbGRNYXBwaW5ncztcblxudmFyIF9yZWFjdCA9IHJlcXVpcmUoJ3JlYWN0Jyk7XG5cbi8qKlxuICogR2l2ZW4gYHRoaXMucHJvcHMuY2hpbGRyZW5gLCByZXR1cm4gYW4gb2JqZWN0IG1hcHBpbmcga2V5IHRvIGNoaWxkLlxuICpcbiAqIEBwYXJhbSB7Kn0gY2hpbGRyZW4gYHRoaXMucHJvcHMuY2hpbGRyZW5gXG4gKiBAcmV0dXJuIHtvYmplY3R9IE1hcHBpbmcgb2Yga2V5IHRvIGNoaWxkXG4gKi9cbmZ1bmN0aW9uIGdldENoaWxkTWFwcGluZyhjaGlsZHJlbikge1xuICBpZiAoIWNoaWxkcmVuKSB7XG4gICAgcmV0dXJuIGNoaWxkcmVuO1xuICB9XG4gIHZhciByZXN1bHQgPSB7fTtcbiAgX3JlYWN0LkNoaWxkcmVuLm1hcChjaGlsZHJlbiwgZnVuY3Rpb24gKGNoaWxkKSB7XG4gICAgcmV0dXJuIGNoaWxkO1xuICB9KS5mb3JFYWNoKGZ1bmN0aW9uIChjaGlsZCkge1xuICAgIHJlc3VsdFtjaGlsZC5rZXldID0gY2hpbGQ7XG4gIH0pO1xuICByZXR1cm4gcmVzdWx0O1xufVxuXG4vKipcbiAqIFdoZW4geW91J3JlIGFkZGluZyBvciByZW1vdmluZyBjaGlsZHJlbiBzb21lIG1heSBiZSBhZGRlZCBvciByZW1vdmVkIGluIHRoZVxuICogc2FtZSByZW5kZXIgcGFzcy4gV2Ugd2FudCB0byBzaG93ICpib3RoKiBzaW5jZSB3ZSB3YW50IHRvIHNpbXVsdGFuZW91c2x5XG4gKiBhbmltYXRlIGVsZW1lbnRzIGluIGFuZCBvdXQuIFRoaXMgZnVuY3Rpb24gdGFrZXMgYSBwcmV2aW91cyBzZXQgb2Yga2V5c1xuICogYW5kIGEgbmV3IHNldCBvZiBrZXlzIGFuZCBtZXJnZXMgdGhlbSB3aXRoIGl0cyBiZXN0IGd1ZXNzIG9mIHRoZSBjb3JyZWN0XG4gKiBvcmRlcmluZy4gSW4gdGhlIGZ1dHVyZSB3ZSBtYXkgZXhwb3NlIHNvbWUgb2YgdGhlIHV0aWxpdGllcyBpblxuICogUmVhY3RNdWx0aUNoaWxkIHRvIG1ha2UgdGhpcyBlYXN5LCBidXQgZm9yIG5vdyBSZWFjdCBpdHNlbGYgZG9lcyBub3RcbiAqIGRpcmVjdGx5IGhhdmUgdGhpcyBjb25jZXB0IG9mIHRoZSB1bmlvbiBvZiBwcmV2Q2hpbGRyZW4gYW5kIG5leHRDaGlsZHJlblxuICogc28gd2UgaW1wbGVtZW50IGl0IGhlcmUuXG4gKlxuICogQHBhcmFtIHtvYmplY3R9IHByZXYgcHJldiBjaGlsZHJlbiBhcyByZXR1cm5lZCBmcm9tXG4gKiBgUmVhY3RUcmFuc2l0aW9uQ2hpbGRNYXBwaW5nLmdldENoaWxkTWFwcGluZygpYC5cbiAqIEBwYXJhbSB7b2JqZWN0fSBuZXh0IG5leHQgY2hpbGRyZW4gYXMgcmV0dXJuZWQgZnJvbVxuICogYFJlYWN0VHJhbnNpdGlvbkNoaWxkTWFwcGluZy5nZXRDaGlsZE1hcHBpbmcoKWAuXG4gKiBAcmV0dXJuIHtvYmplY3R9IGEga2V5IHNldCB0aGF0IGNvbnRhaW5zIGFsbCBrZXlzIGluIGBwcmV2YCBhbmQgYWxsIGtleXNcbiAqIGluIGBuZXh0YCBpbiBhIHJlYXNvbmFibGUgb3JkZXIuXG4gKi9cbmZ1bmN0aW9uIG1lcmdlQ2hpbGRNYXBwaW5ncyhwcmV2LCBuZXh0KSB7XG4gIHByZXYgPSBwcmV2IHx8IHt9O1xuICBuZXh0ID0gbmV4dCB8fCB7fTtcblxuICBmdW5jdGlvbiBnZXRWYWx1ZUZvcktleShrZXkpIHtcbiAgICBpZiAobmV4dC5oYXNPd25Qcm9wZXJ0eShrZXkpKSB7XG4gICAgICByZXR1cm4gbmV4dFtrZXldO1xuICAgIH1cblxuICAgIHJldHVybiBwcmV2W2tleV07XG4gIH1cblxuICAvLyBGb3IgZWFjaCBrZXkgb2YgYG5leHRgLCB0aGUgbGlzdCBvZiBrZXlzIHRvIGluc2VydCBiZWZvcmUgdGhhdCBrZXkgaW5cbiAgLy8gdGhlIGNvbWJpbmVkIGxpc3RcbiAgdmFyIG5leHRLZXlzUGVuZGluZyA9IHt9O1xuXG4gIHZhciBwZW5kaW5nS2V5cyA9IFtdO1xuICBmb3IgKHZhciBwcmV2S2V5IGluIHByZXYpIHtcbiAgICBpZiAobmV4dC5oYXNPd25Qcm9wZXJ0eShwcmV2S2V5KSkge1xuICAgICAgaWYgKHBlbmRpbmdLZXlzLmxlbmd0aCkge1xuICAgICAgICBuZXh0S2V5c1BlbmRpbmdbcHJldktleV0gPSBwZW5kaW5nS2V5cztcbiAgICAgICAgcGVuZGluZ0tleXMgPSBbXTtcbiAgICAgIH1cbiAgICB9IGVsc2Uge1xuICAgICAgcGVuZGluZ0tleXMucHVzaChwcmV2S2V5KTtcbiAgICB9XG4gIH1cblxuICB2YXIgaSA9IHZvaWQgMDtcbiAgdmFyIGNoaWxkTWFwcGluZyA9IHt9O1xuICBmb3IgKHZhciBuZXh0S2V5IGluIG5leHQpIHtcbiAgICBpZiAobmV4dEtleXNQZW5kaW5nLmhhc093blByb3BlcnR5KG5leHRLZXkpKSB7XG4gICAgICBmb3IgKGkgPSAwOyBpIDwgbmV4dEtleXNQZW5kaW5nW25leHRLZXldLmxlbmd0aDsgaSsrKSB7XG4gICAgICAgIHZhciBwZW5kaW5nTmV4dEtleSA9IG5leHRLZXlzUGVuZGluZ1tuZXh0S2V5XVtpXTtcbiAgICAgICAgY2hpbGRNYXBwaW5nW25leHRLZXlzUGVuZGluZ1tuZXh0S2V5XVtpXV0gPSBnZXRWYWx1ZUZvcktleShwZW5kaW5nTmV4dEtleSk7XG4gICAgICB9XG4gICAgfVxuICAgIGNoaWxkTWFwcGluZ1tuZXh0S2V5XSA9IGdldFZhbHVlRm9yS2V5KG5leHRLZXkpO1xuICB9XG5cbiAgLy8gRmluYWxseSwgYWRkIHRoZSBrZXlzIHdoaWNoIGRpZG4ndCBhcHBlYXIgYmVmb3JlIGFueSBrZXkgaW4gYG5leHRgXG4gIGZvciAoaSA9IDA7IGkgPCBwZW5kaW5nS2V5cy5sZW5ndGg7IGkrKykge1xuICAgIGNoaWxkTWFwcGluZ1twZW5kaW5nS2V5c1tpXV0gPSBnZXRWYWx1ZUZvcktleShwZW5kaW5nS2V5c1tpXSk7XG4gIH1cblxuICByZXR1cm4gY2hpbGRNYXBwaW5nO1xufSIsIid1c2Ugc3RyaWN0JztcblxuZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtcblxudmFyIF9leHRlbmRzID0gT2JqZWN0LmFzc2lnbiB8fCBmdW5jdGlvbiAodGFyZ2V0KSB7IGZvciAodmFyIGkgPSAxOyBpIDwgYXJndW1lbnRzLmxlbmd0aDsgaSsrKSB7IHZhciBzb3VyY2UgPSBhcmd1bWVudHNbaV07IGZvciAodmFyIGtleSBpbiBzb3VyY2UpIHsgaWYgKE9iamVjdC5wcm90b3R5cGUuaGFzT3duUHJvcGVydHkuY2FsbChzb3VyY2UsIGtleSkpIHsgdGFyZ2V0W2tleV0gPSBzb3VyY2Vba2V5XTsgfSB9IH0gcmV0dXJuIHRhcmdldDsgfTtcblxudmFyIF9jaGFpbkZ1bmN0aW9uID0gcmVxdWlyZSgnY2hhaW4tZnVuY3Rpb24nKTtcblxudmFyIF9jaGFpbkZ1bmN0aW9uMiA9IF9pbnRlcm9wUmVxdWlyZURlZmF1bHQoX2NoYWluRnVuY3Rpb24pO1xuXG52YXIgX3JlYWN0ID0gcmVxdWlyZSgncmVhY3QnKTtcblxudmFyIF9yZWFjdDIgPSBfaW50ZXJvcFJlcXVpcmVEZWZhdWx0KF9yZWFjdCk7XG5cbnZhciBfcHJvcFR5cGVzID0gcmVxdWlyZSgncHJvcC10eXBlcycpO1xuXG52YXIgX3Byb3BUeXBlczIgPSBfaW50ZXJvcFJlcXVpcmVEZWZhdWx0KF9wcm9wVHlwZXMpO1xuXG52YXIgX3dhcm5pbmcgPSByZXF1aXJlKCd3YXJuaW5nJyk7XG5cbnZhciBfd2FybmluZzIgPSBfaW50ZXJvcFJlcXVpcmVEZWZhdWx0KF93YXJuaW5nKTtcblxudmFyIF9yZWFjdExpZmVjeWNsZXNDb21wYXQgPSByZXF1aXJlKCdyZWFjdC1saWZlY3ljbGVzLWNvbXBhdCcpO1xuXG52YXIgX0NoaWxkTWFwcGluZyA9IHJlcXVpcmUoJy4vdXRpbHMvQ2hpbGRNYXBwaW5nJyk7XG5cbmZ1bmN0aW9uIF9pbnRlcm9wUmVxdWlyZURlZmF1bHQob2JqKSB7IHJldHVybiBvYmogJiYgb2JqLl9fZXNNb2R1bGUgPyBvYmogOiB7IGRlZmF1bHQ6IG9iaiB9OyB9XG5cbmZ1bmN0aW9uIF9jbGFzc0NhbGxDaGVjayhpbnN0YW5jZSwgQ29uc3RydWN0b3IpIHsgaWYgKCEoaW5zdGFuY2UgaW5zdGFuY2VvZiBDb25zdHJ1Y3RvcikpIHsgdGhyb3cgbmV3IFR5cGVFcnJvcihcIkNhbm5vdCBjYWxsIGEgY2xhc3MgYXMgYSBmdW5jdGlvblwiKTsgfSB9XG5cbmZ1bmN0aW9uIF9wb3NzaWJsZUNvbnN0cnVjdG9yUmV0dXJuKHNlbGYsIGNhbGwpIHsgaWYgKCFzZWxmKSB7IHRocm93IG5ldyBSZWZlcmVuY2VFcnJvcihcInRoaXMgaGFzbid0IGJlZW4gaW5pdGlhbGlzZWQgLSBzdXBlcigpIGhhc24ndCBiZWVuIGNhbGxlZFwiKTsgfSByZXR1cm4gY2FsbCAmJiAodHlwZW9mIGNhbGwgPT09IFwib2JqZWN0XCIgfHwgdHlwZW9mIGNhbGwgPT09IFwiZnVuY3Rpb25cIikgPyBjYWxsIDogc2VsZjsgfVxuXG5mdW5jdGlvbiBfaW5oZXJpdHMoc3ViQ2xhc3MsIHN1cGVyQ2xhc3MpIHsgaWYgKHR5cGVvZiBzdXBlckNsYXNzICE9PSBcImZ1bmN0aW9uXCIgJiYgc3VwZXJDbGFzcyAhPT0gbnVsbCkgeyB0aHJvdyBuZXcgVHlwZUVycm9yKFwiU3VwZXIgZXhwcmVzc2lvbiBtdXN0IGVpdGhlciBiZSBudWxsIG9yIGEgZnVuY3Rpb24sIG5vdCBcIiArIHR5cGVvZiBzdXBlckNsYXNzKTsgfSBzdWJDbGFzcy5wcm90b3R5cGUgPSBPYmplY3QuY3JlYXRlKHN1cGVyQ2xhc3MgJiYgc3VwZXJDbGFzcy5wcm90b3R5cGUsIHsgY29uc3RydWN0b3I6IHsgdmFsdWU6IHN1YkNsYXNzLCBlbnVtZXJhYmxlOiBmYWxzZSwgd3JpdGFibGU6IHRydWUsIGNvbmZpZ3VyYWJsZTogdHJ1ZSB9IH0pOyBpZiAoc3VwZXJDbGFzcykgT2JqZWN0LnNldFByb3RvdHlwZU9mID8gT2JqZWN0LnNldFByb3RvdHlwZU9mKHN1YkNsYXNzLCBzdXBlckNsYXNzKSA6IHN1YkNsYXNzLl9fcHJvdG9fXyA9IHN1cGVyQ2xhc3M7IH1cblxudmFyIHByb3BUeXBlcyA9IHtcbiAgY29tcG9uZW50OiBfcHJvcFR5cGVzMi5kZWZhdWx0LmFueSxcbiAgY2hpbGRGYWN0b3J5OiBfcHJvcFR5cGVzMi5kZWZhdWx0LmZ1bmMsXG4gIGNoaWxkcmVuOiBfcHJvcFR5cGVzMi5kZWZhdWx0Lm5vZGVcbn07XG5cbnZhciBkZWZhdWx0UHJvcHMgPSB7XG4gIGNvbXBvbmVudDogJ3NwYW4nLFxuICBjaGlsZEZhY3Rvcnk6IGZ1bmN0aW9uIGNoaWxkRmFjdG9yeShjaGlsZCkge1xuICAgIHJldHVybiBjaGlsZDtcbiAgfVxufTtcblxudmFyIFRyYW5zaXRpb25Hcm91cCA9IGZ1bmN0aW9uIChfUmVhY3QkQ29tcG9uZW50KSB7XG4gIF9pbmhlcml0cyhUcmFuc2l0aW9uR3JvdXAsIF9SZWFjdCRDb21wb25lbnQpO1xuXG4gIGZ1bmN0aW9uIFRyYW5zaXRpb25Hcm91cChwcm9wcywgY29udGV4dCkge1xuICAgIF9jbGFzc0NhbGxDaGVjayh0aGlzLCBUcmFuc2l0aW9uR3JvdXApO1xuXG4gICAgdmFyIF90aGlzID0gX3Bvc3NpYmxlQ29uc3RydWN0b3JSZXR1cm4odGhpcywgX1JlYWN0JENvbXBvbmVudC5jYWxsKHRoaXMsIHByb3BzLCBjb250ZXh0KSk7XG5cbiAgICBfdGhpcy5wZXJmb3JtQXBwZWFyID0gZnVuY3Rpb24gKGtleSwgY29tcG9uZW50KSB7XG4gICAgICBfdGhpcy5jdXJyZW50bHlUcmFuc2l0aW9uaW5nS2V5c1trZXldID0gdHJ1ZTtcblxuICAgICAgaWYgKGNvbXBvbmVudC5jb21wb25lbnRXaWxsQXBwZWFyKSB7XG4gICAgICAgIGNvbXBvbmVudC5jb21wb25lbnRXaWxsQXBwZWFyKF90aGlzLl9oYW5kbGVEb25lQXBwZWFyaW5nLmJpbmQoX3RoaXMsIGtleSwgY29tcG9uZW50KSk7XG4gICAgICB9IGVsc2Uge1xuICAgICAgICBfdGhpcy5faGFuZGxlRG9uZUFwcGVhcmluZyhrZXksIGNvbXBvbmVudCk7XG4gICAgICB9XG4gICAgfTtcblxuICAgIF90aGlzLl9oYW5kbGVEb25lQXBwZWFyaW5nID0gZnVuY3Rpb24gKGtleSwgY29tcG9uZW50KSB7XG4gICAgICBpZiAoY29tcG9uZW50ICYmIGNvbXBvbmVudC5jb21wb25lbnREaWRBcHBlYXIpIHtcbiAgICAgICAgY29tcG9uZW50LmNvbXBvbmVudERpZEFwcGVhcigpO1xuICAgICAgfVxuXG4gICAgICBkZWxldGUgX3RoaXMuY3VycmVudGx5VHJhbnNpdGlvbmluZ0tleXNba2V5XTtcblxuICAgICAgdmFyIGN1cnJlbnRDaGlsZE1hcHBpbmcgPSAoMCwgX0NoaWxkTWFwcGluZy5nZXRDaGlsZE1hcHBpbmcpKF90aGlzLnByb3BzLmNoaWxkcmVuKTtcblxuICAgICAgaWYgKCFjdXJyZW50Q2hpbGRNYXBwaW5nIHx8ICFjdXJyZW50Q2hpbGRNYXBwaW5nLmhhc093blByb3BlcnR5KGtleSkpIHtcbiAgICAgICAgLy8gVGhpcyB3YXMgcmVtb3ZlZCBiZWZvcmUgaXQgaGFkIGZ1bGx5IGFwcGVhcmVkLiBSZW1vdmUgaXQuXG4gICAgICAgIF90aGlzLnBlcmZvcm1MZWF2ZShrZXksIGNvbXBvbmVudCk7XG4gICAgICB9XG4gICAgfTtcblxuICAgIF90aGlzLnBlcmZvcm1FbnRlciA9IGZ1bmN0aW9uIChrZXksIGNvbXBvbmVudCkge1xuICAgICAgX3RoaXMuY3VycmVudGx5VHJhbnNpdGlvbmluZ0tleXNba2V5XSA9IHRydWU7XG5cbiAgICAgIGlmIChjb21wb25lbnQuY29tcG9uZW50V2lsbEVudGVyKSB7XG4gICAgICAgIGNvbXBvbmVudC5jb21wb25lbnRXaWxsRW50ZXIoX3RoaXMuX2hhbmRsZURvbmVFbnRlcmluZy5iaW5kKF90aGlzLCBrZXksIGNvbXBvbmVudCkpO1xuICAgICAgfSBlbHNlIHtcbiAgICAgICAgX3RoaXMuX2hhbmRsZURvbmVFbnRlcmluZyhrZXksIGNvbXBvbmVudCk7XG4gICAgICB9XG4gICAgfTtcblxuICAgIF90aGlzLl9oYW5kbGVEb25lRW50ZXJpbmcgPSBmdW5jdGlvbiAoa2V5LCBjb21wb25lbnQpIHtcbiAgICAgIGlmIChjb21wb25lbnQgJiYgY29tcG9uZW50LmNvbXBvbmVudERpZEVudGVyKSB7XG4gICAgICAgIGNvbXBvbmVudC5jb21wb25lbnREaWRFbnRlcigpO1xuICAgICAgfVxuXG4gICAgICBkZWxldGUgX3RoaXMuY3VycmVudGx5VHJhbnNpdGlvbmluZ0tleXNba2V5XTtcblxuICAgICAgdmFyIGN1cnJlbnRDaGlsZE1hcHBpbmcgPSAoMCwgX0NoaWxkTWFwcGluZy5nZXRDaGlsZE1hcHBpbmcpKF90aGlzLnByb3BzLmNoaWxkcmVuKTtcblxuICAgICAgaWYgKCFjdXJyZW50Q2hpbGRNYXBwaW5nIHx8ICFjdXJyZW50Q2hpbGRNYXBwaW5nLmhhc093blByb3BlcnR5KGtleSkpIHtcbiAgICAgICAgLy8gVGhpcyB3YXMgcmVtb3ZlZCBiZWZvcmUgaXQgaGFkIGZ1bGx5IGVudGVyZWQuIFJlbW92ZSBpdC5cbiAgICAgICAgX3RoaXMucGVyZm9ybUxlYXZlKGtleSwgY29tcG9uZW50KTtcbiAgICAgIH1cbiAgICB9O1xuXG4gICAgX3RoaXMucGVyZm9ybUxlYXZlID0gZnVuY3Rpb24gKGtleSwgY29tcG9uZW50KSB7XG4gICAgICBfdGhpcy5jdXJyZW50bHlUcmFuc2l0aW9uaW5nS2V5c1trZXldID0gdHJ1ZTtcblxuICAgICAgaWYgKGNvbXBvbmVudCAmJiBjb21wb25lbnQuY29tcG9uZW50V2lsbExlYXZlKSB7XG4gICAgICAgIGNvbXBvbmVudC5jb21wb25lbnRXaWxsTGVhdmUoX3RoaXMuX2hhbmRsZURvbmVMZWF2aW5nLmJpbmQoX3RoaXMsIGtleSwgY29tcG9uZW50KSk7XG4gICAgICB9IGVsc2Uge1xuICAgICAgICAvLyBOb3RlIHRoYXQgdGhpcyBpcyBzb21ld2hhdCBkYW5nZXJvdXMgYi9jIGl0IGNhbGxzIHNldFN0YXRlKClcbiAgICAgICAgLy8gYWdhaW4sIGVmZmVjdGl2ZWx5IG11dGF0aW5nIHRoZSBjb21wb25lbnQgYmVmb3JlIGFsbCB0aGUgd29ya1xuICAgICAgICAvLyBpcyBkb25lLlxuICAgICAgICBfdGhpcy5faGFuZGxlRG9uZUxlYXZpbmcoa2V5LCBjb21wb25lbnQpO1xuICAgICAgfVxuICAgIH07XG5cbiAgICBfdGhpcy5faGFuZGxlRG9uZUxlYXZpbmcgPSBmdW5jdGlvbiAoa2V5LCBjb21wb25lbnQpIHtcbiAgICAgIGlmIChjb21wb25lbnQgJiYgY29tcG9uZW50LmNvbXBvbmVudERpZExlYXZlKSB7XG4gICAgICAgIGNvbXBvbmVudC5jb21wb25lbnREaWRMZWF2ZSgpO1xuICAgICAgfVxuXG4gICAgICBkZWxldGUgX3RoaXMuY3VycmVudGx5VHJhbnNpdGlvbmluZ0tleXNba2V5XTtcblxuICAgICAgdmFyIGN1cnJlbnRDaGlsZE1hcHBpbmcgPSAoMCwgX0NoaWxkTWFwcGluZy5nZXRDaGlsZE1hcHBpbmcpKF90aGlzLnByb3BzLmNoaWxkcmVuKTtcblxuICAgICAgaWYgKGN1cnJlbnRDaGlsZE1hcHBpbmcgJiYgY3VycmVudENoaWxkTWFwcGluZy5oYXNPd25Qcm9wZXJ0eShrZXkpKSB7XG4gICAgICAgIC8vIFRoaXMgZW50ZXJlZCBhZ2FpbiBiZWZvcmUgaXQgZnVsbHkgbGVmdC4gQWRkIGl0IGFnYWluLlxuICAgICAgICBfdGhpcy5rZXlzVG9FbnRlci5wdXNoKGtleSk7XG4gICAgICB9IGVsc2Uge1xuICAgICAgICBfdGhpcy5zZXRTdGF0ZShmdW5jdGlvbiAoc3RhdGUpIHtcbiAgICAgICAgICB2YXIgbmV3Q2hpbGRyZW4gPSBfZXh0ZW5kcyh7fSwgc3RhdGUuY2hpbGRyZW4pO1xuICAgICAgICAgIGRlbGV0ZSBuZXdDaGlsZHJlbltrZXldO1xuICAgICAgICAgIHJldHVybiB7IGNoaWxkcmVuOiBuZXdDaGlsZHJlbiB9O1xuICAgICAgICB9KTtcbiAgICAgIH1cbiAgICB9O1xuXG4gICAgX3RoaXMuY2hpbGRSZWZzID0gT2JqZWN0LmNyZWF0ZShudWxsKTtcbiAgICBfdGhpcy5jdXJyZW50bHlUcmFuc2l0aW9uaW5nS2V5cyA9IHt9O1xuICAgIF90aGlzLmtleXNUb0VudGVyID0gW107XG4gICAgX3RoaXMua2V5c1RvTGVhdmUgPSBbXTtcblxuICAgIF90aGlzLnN0YXRlID0ge1xuICAgICAgY2hpbGRyZW46ICgwLCBfQ2hpbGRNYXBwaW5nLmdldENoaWxkTWFwcGluZykocHJvcHMuY2hpbGRyZW4pXG4gICAgfTtcbiAgICByZXR1cm4gX3RoaXM7XG4gIH1cblxuICBUcmFuc2l0aW9uR3JvdXAucHJvdG90eXBlLmNvbXBvbmVudERpZE1vdW50ID0gZnVuY3Rpb24gY29tcG9uZW50RGlkTW91bnQoKSB7XG4gICAgdmFyIGluaXRpYWxDaGlsZE1hcHBpbmcgPSB0aGlzLnN0YXRlLmNoaWxkcmVuO1xuICAgIGZvciAodmFyIGtleSBpbiBpbml0aWFsQ2hpbGRNYXBwaW5nKSB7XG4gICAgICBpZiAoaW5pdGlhbENoaWxkTWFwcGluZ1trZXldKSB7XG4gICAgICAgIHRoaXMucGVyZm9ybUFwcGVhcihrZXksIHRoaXMuY2hpbGRSZWZzW2tleV0pO1xuICAgICAgfVxuICAgIH1cbiAgfTtcblxuICBUcmFuc2l0aW9uR3JvdXAuZ2V0RGVyaXZlZFN0YXRlRnJvbVByb3BzID0gZnVuY3Rpb24gZ2V0RGVyaXZlZFN0YXRlRnJvbVByb3BzKHByb3BzLCBzdGF0ZSkge1xuICAgIHZhciBuZXh0Q2hpbGRNYXBwaW5nID0gKDAsIF9DaGlsZE1hcHBpbmcuZ2V0Q2hpbGRNYXBwaW5nKShwcm9wcy5jaGlsZHJlbik7XG4gICAgdmFyIHByZXZDaGlsZE1hcHBpbmcgPSBzdGF0ZS5jaGlsZHJlbjtcblxuICAgIHJldHVybiB7XG4gICAgICBjaGlsZHJlbjogKDAsIF9DaGlsZE1hcHBpbmcubWVyZ2VDaGlsZE1hcHBpbmdzKShwcmV2Q2hpbGRNYXBwaW5nLCBuZXh0Q2hpbGRNYXBwaW5nKVxuICAgIH07XG4gIH07XG5cbiAgVHJhbnNpdGlvbkdyb3VwLnByb3RvdHlwZS5jb21wb25lbnREaWRVcGRhdGUgPSBmdW5jdGlvbiBjb21wb25lbnREaWRVcGRhdGUocHJldlByb3BzLCBwcmV2U3RhdGUpIHtcbiAgICB2YXIgX3RoaXMyID0gdGhpcztcblxuICAgIHZhciBuZXh0Q2hpbGRNYXBwaW5nID0gKDAsIF9DaGlsZE1hcHBpbmcuZ2V0Q2hpbGRNYXBwaW5nKSh0aGlzLnByb3BzLmNoaWxkcmVuKTtcbiAgICB2YXIgcHJldkNoaWxkTWFwcGluZyA9IHByZXZTdGF0ZS5jaGlsZHJlbjtcblxuICAgIGZvciAodmFyIGtleSBpbiBuZXh0Q2hpbGRNYXBwaW5nKSB7XG4gICAgICB2YXIgaGFzUHJldiA9IHByZXZDaGlsZE1hcHBpbmcgJiYgcHJldkNoaWxkTWFwcGluZy5oYXNPd25Qcm9wZXJ0eShrZXkpO1xuICAgICAgaWYgKG5leHRDaGlsZE1hcHBpbmdba2V5XSAmJiAhaGFzUHJldiAmJiAhdGhpcy5jdXJyZW50bHlUcmFuc2l0aW9uaW5nS2V5c1trZXldKSB7XG4gICAgICAgIHRoaXMua2V5c1RvRW50ZXIucHVzaChrZXkpO1xuICAgICAgfVxuICAgIH1cblxuICAgIGZvciAodmFyIF9rZXkgaW4gcHJldkNoaWxkTWFwcGluZykge1xuICAgICAgdmFyIGhhc05leHQgPSBuZXh0Q2hpbGRNYXBwaW5nICYmIG5leHRDaGlsZE1hcHBpbmcuaGFzT3duUHJvcGVydHkoX2tleSk7XG4gICAgICBpZiAocHJldkNoaWxkTWFwcGluZ1tfa2V5XSAmJiAhaGFzTmV4dCAmJiAhdGhpcy5jdXJyZW50bHlUcmFuc2l0aW9uaW5nS2V5c1tfa2V5XSkge1xuICAgICAgICB0aGlzLmtleXNUb0xlYXZlLnB1c2goX2tleSk7XG4gICAgICB9XG4gICAgfVxuXG4gICAgLy8gSWYgd2Ugd2FudCB0byBzb21lZGF5IGNoZWNrIGZvciByZW9yZGVyaW5nLCB3ZSBjb3VsZCBkbyBpdCBoZXJlLlxuXG4gICAgdmFyIGtleXNUb0VudGVyID0gdGhpcy5rZXlzVG9FbnRlcjtcbiAgICB0aGlzLmtleXNUb0VudGVyID0gW107XG4gICAga2V5c1RvRW50ZXIuZm9yRWFjaChmdW5jdGlvbiAoa2V5KSB7XG4gICAgICByZXR1cm4gX3RoaXMyLnBlcmZvcm1FbnRlcihrZXksIF90aGlzMi5jaGlsZFJlZnNba2V5XSk7XG4gICAgfSk7XG5cbiAgICB2YXIga2V5c1RvTGVhdmUgPSB0aGlzLmtleXNUb0xlYXZlO1xuICAgIHRoaXMua2V5c1RvTGVhdmUgPSBbXTtcbiAgICBrZXlzVG9MZWF2ZS5mb3JFYWNoKGZ1bmN0aW9uIChrZXkpIHtcbiAgICAgIHJldHVybiBfdGhpczIucGVyZm9ybUxlYXZlKGtleSwgX3RoaXMyLmNoaWxkUmVmc1trZXldKTtcbiAgICB9KTtcbiAgfTtcblxuICBUcmFuc2l0aW9uR3JvdXAucHJvdG90eXBlLnJlbmRlciA9IGZ1bmN0aW9uIHJlbmRlcigpIHtcbiAgICB2YXIgX3RoaXMzID0gdGhpcztcblxuICAgIC8vIFRPRE86IHdlIGNvdWxkIGdldCByaWQgb2YgdGhlIG5lZWQgZm9yIHRoZSB3cmFwcGVyIG5vZGVcbiAgICAvLyBieSBjbG9uaW5nIGEgc2luZ2xlIGNoaWxkXG4gICAgdmFyIGNoaWxkcmVuVG9SZW5kZXIgPSBbXTtcblxuICAgIHZhciBfbG9vcCA9IGZ1bmN0aW9uIF9sb29wKGtleSkge1xuICAgICAgdmFyIGNoaWxkID0gX3RoaXMzLnN0YXRlLmNoaWxkcmVuW2tleV07XG4gICAgICBpZiAoY2hpbGQpIHtcbiAgICAgICAgdmFyIGlzQ2FsbGJhY2tSZWYgPSB0eXBlb2YgY2hpbGQucmVmICE9PSAnc3RyaW5nJztcbiAgICAgICAgdmFyIGZhY3RvcnlDaGlsZCA9IF90aGlzMy5wcm9wcy5jaGlsZEZhY3RvcnkoY2hpbGQpO1xuICAgICAgICB2YXIgcmVmID0gZnVuY3Rpb24gcmVmKHIpIHtcbiAgICAgICAgICBfdGhpczMuY2hpbGRSZWZzW2tleV0gPSByO1xuICAgICAgICB9O1xuXG4gICAgICAgIHByb2Nlc3MuZW52Lk5PREVfRU5WICE9PSAncHJvZHVjdGlvbicgPyAoMCwgX3dhcm5pbmcyLmRlZmF1bHQpKGlzQ2FsbGJhY2tSZWYsICdzdHJpbmcgcmVmcyBhcmUgbm90IHN1cHBvcnRlZCBvbiBjaGlsZHJlbiBvZiBUcmFuc2l0aW9uR3JvdXAgYW5kIHdpbGwgYmUgaWdub3JlZC4gJyArICdQbGVhc2UgdXNlIGEgY2FsbGJhY2sgcmVmIGluc3RlYWQ6IGh0dHBzOi8vZmFjZWJvb2suZ2l0aHViLmlvL3JlYWN0L2RvY3MvcmVmcy1hbmQtdGhlLWRvbS5odG1sI3RoZS1yZWYtY2FsbGJhY2stYXR0cmlidXRlJykgOiB2b2lkIDA7XG5cbiAgICAgICAgLy8gQWx3YXlzIGNoYWluaW5nIHRoZSByZWZzIGxlYWRzIHRvIHByb2JsZW1zIHdoZW4gdGhlIGNoaWxkRmFjdG9yeVxuICAgICAgICAvLyB3cmFwcyB0aGUgY2hpbGQuIFRoZSBjaGlsZCByZWYgY2FsbGJhY2sgZ2V0cyBjYWxsZWQgdHdpY2Ugd2l0aCB0aGVcbiAgICAgICAgLy8gd3JhcHBlciBhbmQgdGhlIGNoaWxkLiBTbyB3ZSBvbmx5IG5lZWQgdG8gY2hhaW4gdGhlIHJlZiBpZiB0aGVcbiAgICAgICAgLy8gZmFjdG9yeUNoaWxkIGlzIG5vdCBkaWZmZXJlbnQgZnJvbSBjaGlsZC5cbiAgICAgICAgaWYgKGZhY3RvcnlDaGlsZCA9PT0gY2hpbGQgJiYgaXNDYWxsYmFja1JlZikge1xuICAgICAgICAgIHJlZiA9ICgwLCBfY2hhaW5GdW5jdGlvbjIuZGVmYXVsdCkoY2hpbGQucmVmLCByZWYpO1xuICAgICAgICB9XG5cbiAgICAgICAgLy8gWW91IG1heSBuZWVkIHRvIGFwcGx5IHJlYWN0aXZlIHVwZGF0ZXMgdG8gYSBjaGlsZCBhcyBpdCBpcyBsZWF2aW5nLlxuICAgICAgICAvLyBUaGUgbm9ybWFsIFJlYWN0IHdheSB0byBkbyBpdCB3b24ndCB3b3JrIHNpbmNlIHRoZSBjaGlsZCB3aWxsIGhhdmVcbiAgICAgICAgLy8gYWxyZWFkeSBiZWVuIHJlbW92ZWQuIEluIGNhc2UgeW91IG5lZWQgdGhpcyBiZWhhdmlvciB5b3UgY2FuIHByb3ZpZGVcbiAgICAgICAgLy8gYSBjaGlsZEZhY3RvcnkgZnVuY3Rpb24gdG8gd3JhcCBldmVyeSBjaGlsZCwgZXZlbiB0aGUgb25lcyB0aGF0IGFyZVxuICAgICAgICAvLyBsZWF2aW5nLlxuICAgICAgICBjaGlsZHJlblRvUmVuZGVyLnB1c2goX3JlYWN0Mi5kZWZhdWx0LmNsb25lRWxlbWVudChmYWN0b3J5Q2hpbGQsIHtcbiAgICAgICAgICBrZXk6IGtleSxcbiAgICAgICAgICByZWY6IHJlZlxuICAgICAgICB9KSk7XG4gICAgICB9XG4gICAgfTtcblxuICAgIGZvciAodmFyIGtleSBpbiB0aGlzLnN0YXRlLmNoaWxkcmVuKSB7XG4gICAgICBfbG9vcChrZXkpO1xuICAgIH1cblxuICAgIC8vIERvIG5vdCBmb3J3YXJkIFRyYW5zaXRpb25Hcm91cCBwcm9wcyB0byBwcmltaXRpdmUgRE9NIG5vZGVzXG4gICAgdmFyIHByb3BzID0gX2V4dGVuZHMoe30sIHRoaXMucHJvcHMpO1xuICAgIGRlbGV0ZSBwcm9wcy50cmFuc2l0aW9uTGVhdmU7XG4gICAgZGVsZXRlIHByb3BzLnRyYW5zaXRpb25OYW1lO1xuICAgIGRlbGV0ZSBwcm9wcy50cmFuc2l0aW9uQXBwZWFyO1xuICAgIGRlbGV0ZSBwcm9wcy50cmFuc2l0aW9uRW50ZXI7XG4gICAgZGVsZXRlIHByb3BzLmNoaWxkRmFjdG9yeTtcbiAgICBkZWxldGUgcHJvcHMudHJhbnNpdGlvbkxlYXZlVGltZW91dDtcbiAgICBkZWxldGUgcHJvcHMudHJhbnNpdGlvbkVudGVyVGltZW91dDtcbiAgICBkZWxldGUgcHJvcHMudHJhbnNpdGlvbkFwcGVhclRpbWVvdXQ7XG4gICAgZGVsZXRlIHByb3BzLmNvbXBvbmVudDtcblxuICAgIHJldHVybiBfcmVhY3QyLmRlZmF1bHQuY3JlYXRlRWxlbWVudCh0aGlzLnByb3BzLmNvbXBvbmVudCwgcHJvcHMsIGNoaWxkcmVuVG9SZW5kZXIpO1xuICB9O1xuXG4gIHJldHVybiBUcmFuc2l0aW9uR3JvdXA7XG59KF9yZWFjdDIuZGVmYXVsdC5Db21wb25lbnQpO1xuXG5UcmFuc2l0aW9uR3JvdXAuZGlzcGxheU5hbWUgPSAnVHJhbnNpdGlvbkdyb3VwJztcblxuXG5UcmFuc2l0aW9uR3JvdXAucHJvcFR5cGVzID0gcHJvY2Vzcy5lbnYuTk9ERV9FTlYgIT09IFwicHJvZHVjdGlvblwiID8gcHJvcFR5cGVzIDoge307XG5UcmFuc2l0aW9uR3JvdXAuZGVmYXVsdFByb3BzID0gZGVmYXVsdFByb3BzO1xuXG5leHBvcnRzLmRlZmF1bHQgPSAoMCwgX3JlYWN0TGlmZWN5Y2xlc0NvbXBhdC5wb2x5ZmlsbCkoVHJhbnNpdGlvbkdyb3VwKTtcbm1vZHVsZS5leHBvcnRzID0gZXhwb3J0c1snZGVmYXVsdCddOyIsImZ1bmN0aW9uIF9pbnRlcm9wUmVxdWlyZURlZmF1bHQob2JqKSB7XG4gIHJldHVybiBvYmogJiYgb2JqLl9fZXNNb2R1bGUgPyBvYmogOiB7XG4gICAgXCJkZWZhdWx0XCI6IG9ialxuICB9O1xufVxubW9kdWxlLmV4cG9ydHMgPSBfaW50ZXJvcFJlcXVpcmVEZWZhdWx0LCBtb2R1bGUuZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZSwgbW9kdWxlLmV4cG9ydHNbXCJkZWZhdWx0XCJdID0gbW9kdWxlLmV4cG9ydHM7IiwiXCJ1c2Ugc3RyaWN0XCI7XG5cbmV4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7XG5leHBvcnRzLmRlZmF1bHQgPSBoYXNDbGFzcztcblxuZnVuY3Rpb24gaGFzQ2xhc3MoZWxlbWVudCwgY2xhc3NOYW1lKSB7XG4gIGlmIChlbGVtZW50LmNsYXNzTGlzdCkgcmV0dXJuICEhY2xhc3NOYW1lICYmIGVsZW1lbnQuY2xhc3NMaXN0LmNvbnRhaW5zKGNsYXNzTmFtZSk7ZWxzZSByZXR1cm4gKFwiIFwiICsgKGVsZW1lbnQuY2xhc3NOYW1lLmJhc2VWYWwgfHwgZWxlbWVudC5jbGFzc05hbWUpICsgXCIgXCIpLmluZGV4T2YoXCIgXCIgKyBjbGFzc05hbWUgKyBcIiBcIikgIT09IC0xO1xufVxuXG5tb2R1bGUuZXhwb3J0cyA9IGV4cG9ydHNbXCJkZWZhdWx0XCJdOyIsIlwidXNlIHN0cmljdFwiO1xuXG52YXIgX2ludGVyb3BSZXF1aXJlRGVmYXVsdCA9IHJlcXVpcmUoXCJAYmFiZWwvcnVudGltZS9oZWxwZXJzL2ludGVyb3BSZXF1aXJlRGVmYXVsdFwiKTtcblxuZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtcbmV4cG9ydHMuZGVmYXVsdCA9IGFkZENsYXNzO1xuXG52YXIgX2hhc0NsYXNzID0gX2ludGVyb3BSZXF1aXJlRGVmYXVsdChyZXF1aXJlKFwiLi9oYXNDbGFzc1wiKSk7XG5cbmZ1bmN0aW9uIGFkZENsYXNzKGVsZW1lbnQsIGNsYXNzTmFtZSkge1xuICBpZiAoZWxlbWVudC5jbGFzc0xpc3QpIGVsZW1lbnQuY2xhc3NMaXN0LmFkZChjbGFzc05hbWUpO2Vsc2UgaWYgKCEoMCwgX2hhc0NsYXNzLmRlZmF1bHQpKGVsZW1lbnQsIGNsYXNzTmFtZSkpIGlmICh0eXBlb2YgZWxlbWVudC5jbGFzc05hbWUgPT09ICdzdHJpbmcnKSBlbGVtZW50LmNsYXNzTmFtZSA9IGVsZW1lbnQuY2xhc3NOYW1lICsgJyAnICsgY2xhc3NOYW1lO2Vsc2UgZWxlbWVudC5zZXRBdHRyaWJ1dGUoJ2NsYXNzJywgKGVsZW1lbnQuY2xhc3NOYW1lICYmIGVsZW1lbnQuY2xhc3NOYW1lLmJhc2VWYWwgfHwgJycpICsgJyAnICsgY2xhc3NOYW1lKTtcbn1cblxubW9kdWxlLmV4cG9ydHMgPSBleHBvcnRzW1wiZGVmYXVsdFwiXTsiLCIndXNlIHN0cmljdCc7XG5cbmZ1bmN0aW9uIHJlcGxhY2VDbGFzc05hbWUob3JpZ0NsYXNzLCBjbGFzc1RvUmVtb3ZlKSB7XG4gIHJldHVybiBvcmlnQ2xhc3MucmVwbGFjZShuZXcgUmVnRXhwKCcoXnxcXFxccyknICsgY2xhc3NUb1JlbW92ZSArICcoPzpcXFxcc3wkKScsICdnJyksICckMScpLnJlcGxhY2UoL1xccysvZywgJyAnKS5yZXBsYWNlKC9eXFxzKnxcXHMqJC9nLCAnJyk7XG59XG5cbm1vZHVsZS5leHBvcnRzID0gZnVuY3Rpb24gcmVtb3ZlQ2xhc3MoZWxlbWVudCwgY2xhc3NOYW1lKSB7XG4gIGlmIChlbGVtZW50LmNsYXNzTGlzdCkgZWxlbWVudC5jbGFzc0xpc3QucmVtb3ZlKGNsYXNzTmFtZSk7ZWxzZSBpZiAodHlwZW9mIGVsZW1lbnQuY2xhc3NOYW1lID09PSAnc3RyaW5nJykgZWxlbWVudC5jbGFzc05hbWUgPSByZXBsYWNlQ2xhc3NOYW1lKGVsZW1lbnQuY2xhc3NOYW1lLCBjbGFzc05hbWUpO2Vsc2UgZWxlbWVudC5zZXRBdHRyaWJ1dGUoJ2NsYXNzJywgcmVwbGFjZUNsYXNzTmFtZShlbGVtZW50LmNsYXNzTmFtZSAmJiBlbGVtZW50LmNsYXNzTmFtZS5iYXNlVmFsIHx8ICcnLCBjbGFzc05hbWUpKTtcbn07IiwiXCJ1c2Ugc3RyaWN0XCI7XG5cbmV4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7XG5leHBvcnRzLmRlZmF1bHQgPSB2b2lkIDA7XG5cbnZhciBfZGVmYXVsdCA9ICEhKHR5cGVvZiB3aW5kb3cgIT09ICd1bmRlZmluZWQnICYmIHdpbmRvdy5kb2N1bWVudCAmJiB3aW5kb3cuZG9jdW1lbnQuY3JlYXRlRWxlbWVudCk7XG5cbmV4cG9ydHMuZGVmYXVsdCA9IF9kZWZhdWx0O1xubW9kdWxlLmV4cG9ydHMgPSBleHBvcnRzW1wiZGVmYXVsdFwiXTsiLCJcInVzZSBzdHJpY3RcIjtcblxudmFyIF9pbnRlcm9wUmVxdWlyZURlZmF1bHQgPSByZXF1aXJlKFwiQGJhYmVsL3J1bnRpbWUvaGVscGVycy9pbnRlcm9wUmVxdWlyZURlZmF1bHRcIik7XG5cbmV4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7XG5leHBvcnRzLmRlZmF1bHQgPSB2b2lkIDA7XG5cbnZhciBfaW5ET00gPSBfaW50ZXJvcFJlcXVpcmVEZWZhdWx0KHJlcXVpcmUoXCIuL2luRE9NXCIpKTtcblxudmFyIHZlbmRvcnMgPSBbJycsICd3ZWJraXQnLCAnbW96JywgJ28nLCAnbXMnXTtcbnZhciBjYW5jZWwgPSAnY2xlYXJUaW1lb3V0JztcbnZhciByYWYgPSBmYWxsYmFjaztcbnZhciBjb21wYXRSYWY7XG5cbnZhciBnZXRLZXkgPSBmdW5jdGlvbiBnZXRLZXkodmVuZG9yLCBrKSB7XG4gIHJldHVybiB2ZW5kb3IgKyAoIXZlbmRvciA/IGsgOiBrWzBdLnRvVXBwZXJDYXNlKCkgKyBrLnN1YnN0cigxKSkgKyAnQW5pbWF0aW9uRnJhbWUnO1xufTtcblxuaWYgKF9pbkRPTS5kZWZhdWx0KSB7XG4gIHZlbmRvcnMuc29tZShmdW5jdGlvbiAodmVuZG9yKSB7XG4gICAgdmFyIHJhZktleSA9IGdldEtleSh2ZW5kb3IsICdyZXF1ZXN0Jyk7XG5cbiAgICBpZiAocmFmS2V5IGluIHdpbmRvdykge1xuICAgICAgY2FuY2VsID0gZ2V0S2V5KHZlbmRvciwgJ2NhbmNlbCcpO1xuICAgICAgcmV0dXJuIHJhZiA9IGZ1bmN0aW9uIHJhZihjYikge1xuICAgICAgICByZXR1cm4gd2luZG93W3JhZktleV0oY2IpO1xuICAgICAgfTtcbiAgICB9XG4gIH0pO1xufVxuLyogaHR0cHM6Ly9naXRodWIuY29tL2NvbXBvbmVudC9yYWYgKi9cblxuXG52YXIgcHJldiA9IG5ldyBEYXRlKCkuZ2V0VGltZSgpO1xuXG5mdW5jdGlvbiBmYWxsYmFjayhmbikge1xuICB2YXIgY3VyciA9IG5ldyBEYXRlKCkuZ2V0VGltZSgpLFxuICAgICAgbXMgPSBNYXRoLm1heCgwLCAxNiAtIChjdXJyIC0gcHJldikpLFxuICAgICAgcmVxID0gc2V0VGltZW91dChmbiwgbXMpO1xuICBwcmV2ID0gY3VycjtcbiAgcmV0dXJuIHJlcTtcbn1cblxuY29tcGF0UmFmID0gZnVuY3Rpb24gY29tcGF0UmFmKGNiKSB7XG4gIHJldHVybiByYWYoY2IpO1xufTtcblxuY29tcGF0UmFmLmNhbmNlbCA9IGZ1bmN0aW9uIChpZCkge1xuICB3aW5kb3dbY2FuY2VsXSAmJiB0eXBlb2Ygd2luZG93W2NhbmNlbF0gPT09ICdmdW5jdGlvbicgJiYgd2luZG93W2NhbmNlbF0oaWQpO1xufTtcblxudmFyIF9kZWZhdWx0ID0gY29tcGF0UmFmO1xuZXhwb3J0cy5kZWZhdWx0ID0gX2RlZmF1bHQ7XG5tb2R1bGUuZXhwb3J0cyA9IGV4cG9ydHNbXCJkZWZhdWx0XCJdOyIsIlwidXNlIHN0cmljdFwiO1xuXG52YXIgX2ludGVyb3BSZXF1aXJlRGVmYXVsdCA9IHJlcXVpcmUoXCJAYmFiZWwvcnVudGltZS9oZWxwZXJzL2ludGVyb3BSZXF1aXJlRGVmYXVsdFwiKTtcblxuZXhwb3J0cy5fX2VzTW9kdWxlID0gdHJ1ZTtcbmV4cG9ydHMuZGVmYXVsdCA9IGV4cG9ydHMuYW5pbWF0aW9uRW5kID0gZXhwb3J0cy5hbmltYXRpb25EZWxheSA9IGV4cG9ydHMuYW5pbWF0aW9uVGltaW5nID0gZXhwb3J0cy5hbmltYXRpb25EdXJhdGlvbiA9IGV4cG9ydHMuYW5pbWF0aW9uTmFtZSA9IGV4cG9ydHMudHJhbnNpdGlvbkVuZCA9IGV4cG9ydHMudHJhbnNpdGlvbkR1cmF0aW9uID0gZXhwb3J0cy50cmFuc2l0aW9uRGVsYXkgPSBleHBvcnRzLnRyYW5zaXRpb25UaW1pbmcgPSBleHBvcnRzLnRyYW5zaXRpb25Qcm9wZXJ0eSA9IGV4cG9ydHMudHJhbnNmb3JtID0gdm9pZCAwO1xuXG52YXIgX2luRE9NID0gX2ludGVyb3BSZXF1aXJlRGVmYXVsdChyZXF1aXJlKFwiLi4vdXRpbC9pbkRPTVwiKSk7XG5cbnZhciB0cmFuc2Zvcm0gPSAndHJhbnNmb3JtJztcbmV4cG9ydHMudHJhbnNmb3JtID0gdHJhbnNmb3JtO1xudmFyIHByZWZpeCwgdHJhbnNpdGlvbkVuZCwgYW5pbWF0aW9uRW5kO1xuZXhwb3J0cy5hbmltYXRpb25FbmQgPSBhbmltYXRpb25FbmQ7XG5leHBvcnRzLnRyYW5zaXRpb25FbmQgPSB0cmFuc2l0aW9uRW5kO1xudmFyIHRyYW5zaXRpb25Qcm9wZXJ0eSwgdHJhbnNpdGlvbkR1cmF0aW9uLCB0cmFuc2l0aW9uVGltaW5nLCB0cmFuc2l0aW9uRGVsYXk7XG5leHBvcnRzLnRyYW5zaXRpb25EZWxheSA9IHRyYW5zaXRpb25EZWxheTtcbmV4cG9ydHMudHJhbnNpdGlvblRpbWluZyA9IHRyYW5zaXRpb25UaW1pbmc7XG5leHBvcnRzLnRyYW5zaXRpb25EdXJhdGlvbiA9IHRyYW5zaXRpb25EdXJhdGlvbjtcbmV4cG9ydHMudHJhbnNpdGlvblByb3BlcnR5ID0gdHJhbnNpdGlvblByb3BlcnR5O1xudmFyIGFuaW1hdGlvbk5hbWUsIGFuaW1hdGlvbkR1cmF0aW9uLCBhbmltYXRpb25UaW1pbmcsIGFuaW1hdGlvbkRlbGF5O1xuZXhwb3J0cy5hbmltYXRpb25EZWxheSA9IGFuaW1hdGlvbkRlbGF5O1xuZXhwb3J0cy5hbmltYXRpb25UaW1pbmcgPSBhbmltYXRpb25UaW1pbmc7XG5leHBvcnRzLmFuaW1hdGlvbkR1cmF0aW9uID0gYW5pbWF0aW9uRHVyYXRpb247XG5leHBvcnRzLmFuaW1hdGlvbk5hbWUgPSBhbmltYXRpb25OYW1lO1xuXG5pZiAoX2luRE9NLmRlZmF1bHQpIHtcbiAgdmFyIF9nZXRUcmFuc2l0aW9uUHJvcGVydCA9IGdldFRyYW5zaXRpb25Qcm9wZXJ0aWVzKCk7XG5cbiAgcHJlZml4ID0gX2dldFRyYW5zaXRpb25Qcm9wZXJ0LnByZWZpeDtcbiAgZXhwb3J0cy50cmFuc2l0aW9uRW5kID0gdHJhbnNpdGlvbkVuZCA9IF9nZXRUcmFuc2l0aW9uUHJvcGVydC50cmFuc2l0aW9uRW5kO1xuICBleHBvcnRzLmFuaW1hdGlvbkVuZCA9IGFuaW1hdGlvbkVuZCA9IF9nZXRUcmFuc2l0aW9uUHJvcGVydC5hbmltYXRpb25FbmQ7XG4gIGV4cG9ydHMudHJhbnNmb3JtID0gdHJhbnNmb3JtID0gcHJlZml4ICsgXCItXCIgKyB0cmFuc2Zvcm07XG4gIGV4cG9ydHMudHJhbnNpdGlvblByb3BlcnR5ID0gdHJhbnNpdGlvblByb3BlcnR5ID0gcHJlZml4ICsgXCItdHJhbnNpdGlvbi1wcm9wZXJ0eVwiO1xuICBleHBvcnRzLnRyYW5zaXRpb25EdXJhdGlvbiA9IHRyYW5zaXRpb25EdXJhdGlvbiA9IHByZWZpeCArIFwiLXRyYW5zaXRpb24tZHVyYXRpb25cIjtcbiAgZXhwb3J0cy50cmFuc2l0aW9uRGVsYXkgPSB0cmFuc2l0aW9uRGVsYXkgPSBwcmVmaXggKyBcIi10cmFuc2l0aW9uLWRlbGF5XCI7XG4gIGV4cG9ydHMudHJhbnNpdGlvblRpbWluZyA9IHRyYW5zaXRpb25UaW1pbmcgPSBwcmVmaXggKyBcIi10cmFuc2l0aW9uLXRpbWluZy1mdW5jdGlvblwiO1xuICBleHBvcnRzLmFuaW1hdGlvbk5hbWUgPSBhbmltYXRpb25OYW1lID0gcHJlZml4ICsgXCItYW5pbWF0aW9uLW5hbWVcIjtcbiAgZXhwb3J0cy5hbmltYXRpb25EdXJhdGlvbiA9IGFuaW1hdGlvbkR1cmF0aW9uID0gcHJlZml4ICsgXCItYW5pbWF0aW9uLWR1cmF0aW9uXCI7XG4gIGV4cG9ydHMuYW5pbWF0aW9uVGltaW5nID0gYW5pbWF0aW9uVGltaW5nID0gcHJlZml4ICsgXCItYW5pbWF0aW9uLWRlbGF5XCI7XG4gIGV4cG9ydHMuYW5pbWF0aW9uRGVsYXkgPSBhbmltYXRpb25EZWxheSA9IHByZWZpeCArIFwiLWFuaW1hdGlvbi10aW1pbmctZnVuY3Rpb25cIjtcbn1cblxudmFyIF9kZWZhdWx0ID0ge1xuICB0cmFuc2Zvcm06IHRyYW5zZm9ybSxcbiAgZW5kOiB0cmFuc2l0aW9uRW5kLFxuICBwcm9wZXJ0eTogdHJhbnNpdGlvblByb3BlcnR5LFxuICB0aW1pbmc6IHRyYW5zaXRpb25UaW1pbmcsXG4gIGRlbGF5OiB0cmFuc2l0aW9uRGVsYXksXG4gIGR1cmF0aW9uOiB0cmFuc2l0aW9uRHVyYXRpb25cbn07XG5leHBvcnRzLmRlZmF1bHQgPSBfZGVmYXVsdDtcblxuZnVuY3Rpb24gZ2V0VHJhbnNpdGlvblByb3BlcnRpZXMoKSB7XG4gIHZhciBzdHlsZSA9IGRvY3VtZW50LmNyZWF0ZUVsZW1lbnQoJ2RpdicpLnN0eWxlO1xuICB2YXIgdmVuZG9yTWFwID0ge1xuICAgIE86IGZ1bmN0aW9uIE8oZSkge1xuICAgICAgcmV0dXJuIFwib1wiICsgZS50b0xvd2VyQ2FzZSgpO1xuICAgIH0sXG4gICAgTW96OiBmdW5jdGlvbiBNb3ooZSkge1xuICAgICAgcmV0dXJuIGUudG9Mb3dlckNhc2UoKTtcbiAgICB9LFxuICAgIFdlYmtpdDogZnVuY3Rpb24gV2Via2l0KGUpIHtcbiAgICAgIHJldHVybiBcIndlYmtpdFwiICsgZTtcbiAgICB9LFxuICAgIG1zOiBmdW5jdGlvbiBtcyhlKSB7XG4gICAgICByZXR1cm4gXCJNU1wiICsgZTtcbiAgICB9XG4gIH07XG4gIHZhciB2ZW5kb3JzID0gT2JqZWN0LmtleXModmVuZG9yTWFwKTtcbiAgdmFyIHRyYW5zaXRpb25FbmQsIGFuaW1hdGlvbkVuZDtcbiAgdmFyIHByZWZpeCA9ICcnO1xuXG4gIGZvciAodmFyIGkgPSAwOyBpIDwgdmVuZG9ycy5sZW5ndGg7IGkrKykge1xuICAgIHZhciB2ZW5kb3IgPSB2ZW5kb3JzW2ldO1xuXG4gICAgaWYgKHZlbmRvciArIFwiVHJhbnNpdGlvblByb3BlcnR5XCIgaW4gc3R5bGUpIHtcbiAgICAgIHByZWZpeCA9IFwiLVwiICsgdmVuZG9yLnRvTG93ZXJDYXNlKCk7XG4gICAgICB0cmFuc2l0aW9uRW5kID0gdmVuZG9yTWFwW3ZlbmRvcl0oJ1RyYW5zaXRpb25FbmQnKTtcbiAgICAgIGFuaW1hdGlvbkVuZCA9IHZlbmRvck1hcFt2ZW5kb3JdKCdBbmltYXRpb25FbmQnKTtcbiAgICAgIGJyZWFrO1xuICAgIH1cbiAgfVxuXG4gIGlmICghdHJhbnNpdGlvbkVuZCAmJiAndHJhbnNpdGlvblByb3BlcnR5JyBpbiBzdHlsZSkgdHJhbnNpdGlvbkVuZCA9ICd0cmFuc2l0aW9uZW5kJztcbiAgaWYgKCFhbmltYXRpb25FbmQgJiYgJ2FuaW1hdGlvbk5hbWUnIGluIHN0eWxlKSBhbmltYXRpb25FbmQgPSAnYW5pbWF0aW9uZW5kJztcbiAgc3R5bGUgPSBudWxsO1xuICByZXR1cm4ge1xuICAgIGFuaW1hdGlvbkVuZDogYW5pbWF0aW9uRW5kLFxuICAgIHRyYW5zaXRpb25FbmQ6IHRyYW5zaXRpb25FbmQsXG4gICAgcHJlZml4OiBwcmVmaXhcbiAgfTtcbn0iLCIndXNlIHN0cmljdCc7XG5cbmV4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7XG5leHBvcnRzLm5hbWVTaGFwZSA9IHVuZGVmaW5lZDtcbmV4cG9ydHMudHJhbnNpdGlvblRpbWVvdXQgPSB0cmFuc2l0aW9uVGltZW91dDtcblxudmFyIF9yZWFjdCA9IHJlcXVpcmUoJ3JlYWN0Jyk7XG5cbnZhciBfcmVhY3QyID0gX2ludGVyb3BSZXF1aXJlRGVmYXVsdChfcmVhY3QpO1xuXG52YXIgX3Byb3BUeXBlcyA9IHJlcXVpcmUoJ3Byb3AtdHlwZXMnKTtcblxudmFyIF9wcm9wVHlwZXMyID0gX2ludGVyb3BSZXF1aXJlRGVmYXVsdChfcHJvcFR5cGVzKTtcblxuZnVuY3Rpb24gX2ludGVyb3BSZXF1aXJlRGVmYXVsdChvYmopIHsgcmV0dXJuIG9iaiAmJiBvYmouX19lc01vZHVsZSA/IG9iaiA6IHsgZGVmYXVsdDogb2JqIH07IH1cblxuZnVuY3Rpb24gdHJhbnNpdGlvblRpbWVvdXQodHJhbnNpdGlvblR5cGUpIHtcbiAgdmFyIHRpbWVvdXRQcm9wTmFtZSA9ICd0cmFuc2l0aW9uJyArIHRyYW5zaXRpb25UeXBlICsgJ1RpbWVvdXQnO1xuICB2YXIgZW5hYmxlZFByb3BOYW1lID0gJ3RyYW5zaXRpb24nICsgdHJhbnNpdGlvblR5cGU7XG5cbiAgcmV0dXJuIGZ1bmN0aW9uIChwcm9wcykge1xuICAgIC8vIElmIHRoZSB0cmFuc2l0aW9uIGlzIGVuYWJsZWRcbiAgICBpZiAocHJvcHNbZW5hYmxlZFByb3BOYW1lXSkge1xuICAgICAgLy8gSWYgbm8gdGltZW91dCBkdXJhdGlvbiBpcyBwcm92aWRlZFxuICAgICAgaWYgKHByb3BzW3RpbWVvdXRQcm9wTmFtZV0gPT0gbnVsbCkge1xuICAgICAgICByZXR1cm4gbmV3IEVycm9yKHRpbWVvdXRQcm9wTmFtZSArICcgd2FzblxcJ3Qgc3VwcGxpZWQgdG8gQ1NTVHJhbnNpdGlvbkdyb3VwOiAnICsgJ3RoaXMgY2FuIGNhdXNlIHVucmVsaWFibGUgYW5pbWF0aW9ucyBhbmQgd29uXFwndCBiZSBzdXBwb3J0ZWQgaW4gJyArICdhIGZ1dHVyZSB2ZXJzaW9uIG9mIFJlYWN0LiBTZWUgJyArICdodHRwczovL2ZiLm1lL3JlYWN0LWFuaW1hdGlvbi10cmFuc2l0aW9uLWdyb3VwLXRpbWVvdXQgZm9yIG1vcmUgJyArICdpbmZvcm1hdGlvbi4nKTtcblxuICAgICAgICAvLyBJZiB0aGUgZHVyYXRpb24gaXNuJ3QgYSBudW1iZXJcbiAgICAgIH0gZWxzZSBpZiAodHlwZW9mIHByb3BzW3RpbWVvdXRQcm9wTmFtZV0gIT09ICdudW1iZXInKSB7XG4gICAgICAgIHJldHVybiBuZXcgRXJyb3IodGltZW91dFByb3BOYW1lICsgJyBtdXN0IGJlIGEgbnVtYmVyIChpbiBtaWxsaXNlY29uZHMpJyk7XG4gICAgICB9XG4gICAgfVxuXG4gICAgcmV0dXJuIG51bGw7XG4gIH07XG59XG5cbnZhciBuYW1lU2hhcGUgPSBleHBvcnRzLm5hbWVTaGFwZSA9IF9wcm9wVHlwZXMyLmRlZmF1bHQub25lT2ZUeXBlKFtfcHJvcFR5cGVzMi5kZWZhdWx0LnN0cmluZywgX3Byb3BUeXBlczIuZGVmYXVsdC5zaGFwZSh7XG4gIGVudGVyOiBfcHJvcFR5cGVzMi5kZWZhdWx0LnN0cmluZyxcbiAgbGVhdmU6IF9wcm9wVHlwZXMyLmRlZmF1bHQuc3RyaW5nLFxuICBhY3RpdmU6IF9wcm9wVHlwZXMyLmRlZmF1bHQuc3RyaW5nXG59KSwgX3Byb3BUeXBlczIuZGVmYXVsdC5zaGFwZSh7XG4gIGVudGVyOiBfcHJvcFR5cGVzMi5kZWZhdWx0LnN0cmluZyxcbiAgZW50ZXJBY3RpdmU6IF9wcm9wVHlwZXMyLmRlZmF1bHQuc3RyaW5nLFxuICBsZWF2ZTogX3Byb3BUeXBlczIuZGVmYXVsdC5zdHJpbmcsXG4gIGxlYXZlQWN0aXZlOiBfcHJvcFR5cGVzMi5kZWZhdWx0LnN0cmluZyxcbiAgYXBwZWFyOiBfcHJvcFR5cGVzMi5kZWZhdWx0LnN0cmluZyxcbiAgYXBwZWFyQWN0aXZlOiBfcHJvcFR5cGVzMi5kZWZhdWx0LnN0cmluZ1xufSldKTsiLCIndXNlIHN0cmljdCc7XG5cbmV4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7XG5cbnZhciBfZXh0ZW5kcyA9IE9iamVjdC5hc3NpZ24gfHwgZnVuY3Rpb24gKHRhcmdldCkgeyBmb3IgKHZhciBpID0gMTsgaSA8IGFyZ3VtZW50cy5sZW5ndGg7IGkrKykgeyB2YXIgc291cmNlID0gYXJndW1lbnRzW2ldOyBmb3IgKHZhciBrZXkgaW4gc291cmNlKSB7IGlmIChPYmplY3QucHJvdG90eXBlLmhhc093blByb3BlcnR5LmNhbGwoc291cmNlLCBrZXkpKSB7IHRhcmdldFtrZXldID0gc291cmNlW2tleV07IH0gfSB9IHJldHVybiB0YXJnZXQ7IH07XG5cbnZhciBfYWRkQ2xhc3MgPSByZXF1aXJlKCdkb20taGVscGVycy9jbGFzcy9hZGRDbGFzcycpO1xuXG52YXIgX2FkZENsYXNzMiA9IF9pbnRlcm9wUmVxdWlyZURlZmF1bHQoX2FkZENsYXNzKTtcblxudmFyIF9yZW1vdmVDbGFzcyA9IHJlcXVpcmUoJ2RvbS1oZWxwZXJzL2NsYXNzL3JlbW92ZUNsYXNzJyk7XG5cbnZhciBfcmVtb3ZlQ2xhc3MyID0gX2ludGVyb3BSZXF1aXJlRGVmYXVsdChfcmVtb3ZlQ2xhc3MpO1xuXG52YXIgX3JlcXVlc3RBbmltYXRpb25GcmFtZSA9IHJlcXVpcmUoJ2RvbS1oZWxwZXJzL3V0aWwvcmVxdWVzdEFuaW1hdGlvbkZyYW1lJyk7XG5cbnZhciBfcmVxdWVzdEFuaW1hdGlvbkZyYW1lMiA9IF9pbnRlcm9wUmVxdWlyZURlZmF1bHQoX3JlcXVlc3RBbmltYXRpb25GcmFtZSk7XG5cbnZhciBfcHJvcGVydGllcyA9IHJlcXVpcmUoJ2RvbS1oZWxwZXJzL3RyYW5zaXRpb24vcHJvcGVydGllcycpO1xuXG52YXIgX3JlYWN0ID0gcmVxdWlyZSgncmVhY3QnKTtcblxudmFyIF9yZWFjdDIgPSBfaW50ZXJvcFJlcXVpcmVEZWZhdWx0KF9yZWFjdCk7XG5cbnZhciBfcHJvcFR5cGVzID0gcmVxdWlyZSgncHJvcC10eXBlcycpO1xuXG52YXIgX3Byb3BUeXBlczIgPSBfaW50ZXJvcFJlcXVpcmVEZWZhdWx0KF9wcm9wVHlwZXMpO1xuXG52YXIgX3JlYWN0RG9tID0gcmVxdWlyZSgncmVhY3QtZG9tJyk7XG5cbnZhciBfUHJvcFR5cGVzID0gcmVxdWlyZSgnLi91dGlscy9Qcm9wVHlwZXMnKTtcblxuZnVuY3Rpb24gX2ludGVyb3BSZXF1aXJlRGVmYXVsdChvYmopIHsgcmV0dXJuIG9iaiAmJiBvYmouX19lc01vZHVsZSA/IG9iaiA6IHsgZGVmYXVsdDogb2JqIH07IH1cblxuZnVuY3Rpb24gX2NsYXNzQ2FsbENoZWNrKGluc3RhbmNlLCBDb25zdHJ1Y3RvcikgeyBpZiAoIShpbnN0YW5jZSBpbnN0YW5jZW9mIENvbnN0cnVjdG9yKSkgeyB0aHJvdyBuZXcgVHlwZUVycm9yKFwiQ2Fubm90IGNhbGwgYSBjbGFzcyBhcyBhIGZ1bmN0aW9uXCIpOyB9IH1cblxuZnVuY3Rpb24gX3Bvc3NpYmxlQ29uc3RydWN0b3JSZXR1cm4oc2VsZiwgY2FsbCkgeyBpZiAoIXNlbGYpIHsgdGhyb3cgbmV3IFJlZmVyZW5jZUVycm9yKFwidGhpcyBoYXNuJ3QgYmVlbiBpbml0aWFsaXNlZCAtIHN1cGVyKCkgaGFzbid0IGJlZW4gY2FsbGVkXCIpOyB9IHJldHVybiBjYWxsICYmICh0eXBlb2YgY2FsbCA9PT0gXCJvYmplY3RcIiB8fCB0eXBlb2YgY2FsbCA9PT0gXCJmdW5jdGlvblwiKSA/IGNhbGwgOiBzZWxmOyB9XG5cbmZ1bmN0aW9uIF9pbmhlcml0cyhzdWJDbGFzcywgc3VwZXJDbGFzcykgeyBpZiAodHlwZW9mIHN1cGVyQ2xhc3MgIT09IFwiZnVuY3Rpb25cIiAmJiBzdXBlckNsYXNzICE9PSBudWxsKSB7IHRocm93IG5ldyBUeXBlRXJyb3IoXCJTdXBlciBleHByZXNzaW9uIG11c3QgZWl0aGVyIGJlIG51bGwgb3IgYSBmdW5jdGlvbiwgbm90IFwiICsgdHlwZW9mIHN1cGVyQ2xhc3MpOyB9IHN1YkNsYXNzLnByb3RvdHlwZSA9IE9iamVjdC5jcmVhdGUoc3VwZXJDbGFzcyAmJiBzdXBlckNsYXNzLnByb3RvdHlwZSwgeyBjb25zdHJ1Y3RvcjogeyB2YWx1ZTogc3ViQ2xhc3MsIGVudW1lcmFibGU6IGZhbHNlLCB3cml0YWJsZTogdHJ1ZSwgY29uZmlndXJhYmxlOiB0cnVlIH0gfSk7IGlmIChzdXBlckNsYXNzKSBPYmplY3Quc2V0UHJvdG90eXBlT2YgPyBPYmplY3Quc2V0UHJvdG90eXBlT2Yoc3ViQ2xhc3MsIHN1cGVyQ2xhc3MpIDogc3ViQ2xhc3MuX19wcm90b19fID0gc3VwZXJDbGFzczsgfVxuXG52YXIgZXZlbnRzID0gW107XG5pZiAoX3Byb3BlcnRpZXMudHJhbnNpdGlvbkVuZCkgZXZlbnRzLnB1c2goX3Byb3BlcnRpZXMudHJhbnNpdGlvbkVuZCk7XG5pZiAoX3Byb3BlcnRpZXMuYW5pbWF0aW9uRW5kKSBldmVudHMucHVzaChfcHJvcGVydGllcy5hbmltYXRpb25FbmQpO1xuXG5mdW5jdGlvbiBhZGRFbmRMaXN0ZW5lcihub2RlLCBsaXN0ZW5lcikge1xuICBpZiAoZXZlbnRzLmxlbmd0aCkge1xuICAgIGV2ZW50cy5mb3JFYWNoKGZ1bmN0aW9uIChlKSB7XG4gICAgICByZXR1cm4gbm9kZS5hZGRFdmVudExpc3RlbmVyKGUsIGxpc3RlbmVyLCBmYWxzZSk7XG4gICAgfSk7XG4gIH0gZWxzZSB7XG4gICAgc2V0VGltZW91dChsaXN0ZW5lciwgMCk7XG4gIH1cblxuICByZXR1cm4gZnVuY3Rpb24gKCkge1xuICAgIGlmICghZXZlbnRzLmxlbmd0aCkgcmV0dXJuO1xuICAgIGV2ZW50cy5mb3JFYWNoKGZ1bmN0aW9uIChlKSB7XG4gICAgICByZXR1cm4gbm9kZS5yZW1vdmVFdmVudExpc3RlbmVyKGUsIGxpc3RlbmVyLCBmYWxzZSk7XG4gICAgfSk7XG4gIH07XG59XG5cbnZhciBwcm9wVHlwZXMgPSB7XG4gIGNoaWxkcmVuOiBfcHJvcFR5cGVzMi5kZWZhdWx0Lm5vZGUsXG4gIG5hbWU6IF9Qcm9wVHlwZXMubmFtZVNoYXBlLmlzUmVxdWlyZWQsXG5cbiAgLy8gT25jZSB3ZSByZXF1aXJlIHRpbWVvdXRzIHRvIGJlIHNwZWNpZmllZCwgd2UgY2FuIHJlbW92ZSB0aGVcbiAgLy8gYm9vbGVhbiBmbGFncyAoYXBwZWFyIGV0Yy4pIGFuZCBqdXN0IGFjY2VwdCBhIG51bWJlclxuICAvLyBvciBhIGJvb2wgZm9yIHRoZSB0aW1lb3V0IGZsYWdzIChhcHBlYXJUaW1lb3V0IGV0Yy4pXG4gIGFwcGVhcjogX3Byb3BUeXBlczIuZGVmYXVsdC5ib29sLFxuICBlbnRlcjogX3Byb3BUeXBlczIuZGVmYXVsdC5ib29sLFxuICBsZWF2ZTogX3Byb3BUeXBlczIuZGVmYXVsdC5ib29sLFxuICBhcHBlYXJUaW1lb3V0OiBfcHJvcFR5cGVzMi5kZWZhdWx0Lm51bWJlcixcbiAgZW50ZXJUaW1lb3V0OiBfcHJvcFR5cGVzMi5kZWZhdWx0Lm51bWJlcixcbiAgbGVhdmVUaW1lb3V0OiBfcHJvcFR5cGVzMi5kZWZhdWx0Lm51bWJlclxufTtcblxudmFyIENTU1RyYW5zaXRpb25Hcm91cENoaWxkID0gZnVuY3Rpb24gKF9SZWFjdCRDb21wb25lbnQpIHtcbiAgX2luaGVyaXRzKENTU1RyYW5zaXRpb25Hcm91cENoaWxkLCBfUmVhY3QkQ29tcG9uZW50KTtcblxuICBmdW5jdGlvbiBDU1NUcmFuc2l0aW9uR3JvdXBDaGlsZChwcm9wcywgY29udGV4dCkge1xuICAgIF9jbGFzc0NhbGxDaGVjayh0aGlzLCBDU1NUcmFuc2l0aW9uR3JvdXBDaGlsZCk7XG5cbiAgICB2YXIgX3RoaXMgPSBfcG9zc2libGVDb25zdHJ1Y3RvclJldHVybih0aGlzLCBfUmVhY3QkQ29tcG9uZW50LmNhbGwodGhpcywgcHJvcHMsIGNvbnRleHQpKTtcblxuICAgIF90aGlzLmNvbXBvbmVudFdpbGxBcHBlYXIgPSBmdW5jdGlvbiAoZG9uZSkge1xuICAgICAgaWYgKF90aGlzLnByb3BzLmFwcGVhcikge1xuICAgICAgICBfdGhpcy50cmFuc2l0aW9uKCdhcHBlYXInLCBkb25lLCBfdGhpcy5wcm9wcy5hcHBlYXJUaW1lb3V0KTtcbiAgICAgIH0gZWxzZSB7XG4gICAgICAgIGRvbmUoKTtcbiAgICAgIH1cbiAgICB9O1xuXG4gICAgX3RoaXMuY29tcG9uZW50V2lsbEVudGVyID0gZnVuY3Rpb24gKGRvbmUpIHtcbiAgICAgIGlmIChfdGhpcy5wcm9wcy5lbnRlcikge1xuICAgICAgICBfdGhpcy50cmFuc2l0aW9uKCdlbnRlcicsIGRvbmUsIF90aGlzLnByb3BzLmVudGVyVGltZW91dCk7XG4gICAgICB9IGVsc2Uge1xuICAgICAgICBkb25lKCk7XG4gICAgICB9XG4gICAgfTtcblxuICAgIF90aGlzLmNvbXBvbmVudFdpbGxMZWF2ZSA9IGZ1bmN0aW9uIChkb25lKSB7XG4gICAgICBpZiAoX3RoaXMucHJvcHMubGVhdmUpIHtcbiAgICAgICAgX3RoaXMudHJhbnNpdGlvbignbGVhdmUnLCBkb25lLCBfdGhpcy5wcm9wcy5sZWF2ZVRpbWVvdXQpO1xuICAgICAgfSBlbHNlIHtcbiAgICAgICAgZG9uZSgpO1xuICAgICAgfVxuICAgIH07XG5cbiAgICBfdGhpcy5jbGFzc05hbWVBbmROb2RlUXVldWUgPSBbXTtcbiAgICBfdGhpcy50cmFuc2l0aW9uVGltZW91dHMgPSBbXTtcbiAgICByZXR1cm4gX3RoaXM7XG4gIH1cblxuICBDU1NUcmFuc2l0aW9uR3JvdXBDaGlsZC5wcm90b3R5cGUuY29tcG9uZW50V2lsbFVubW91bnQgPSBmdW5jdGlvbiBjb21wb25lbnRXaWxsVW5tb3VudCgpIHtcbiAgICB0aGlzLnVubW91bnRlZCA9IHRydWU7XG5cbiAgICBpZiAodGhpcy50aW1lb3V0KSB7XG4gICAgICBjbGVhclRpbWVvdXQodGhpcy50aW1lb3V0KTtcbiAgICB9XG4gICAgdGhpcy50cmFuc2l0aW9uVGltZW91dHMuZm9yRWFjaChmdW5jdGlvbiAodGltZW91dCkge1xuICAgICAgY2xlYXJUaW1lb3V0KHRpbWVvdXQpO1xuICAgIH0pO1xuXG4gICAgdGhpcy5jbGFzc05hbWVBbmROb2RlUXVldWUubGVuZ3RoID0gMDtcbiAgfTtcblxuICBDU1NUcmFuc2l0aW9uR3JvdXBDaGlsZC5wcm90b3R5cGUudHJhbnNpdGlvbiA9IGZ1bmN0aW9uIHRyYW5zaXRpb24oYW5pbWF0aW9uVHlwZSwgZmluaXNoQ2FsbGJhY2ssIHRpbWVvdXQpIHtcbiAgICB2YXIgbm9kZSA9ICgwLCBfcmVhY3REb20uZmluZERPTU5vZGUpKHRoaXMpO1xuXG4gICAgaWYgKCFub2RlKSB7XG4gICAgICBpZiAoZmluaXNoQ2FsbGJhY2spIHtcbiAgICAgICAgZmluaXNoQ2FsbGJhY2soKTtcbiAgICAgIH1cbiAgICAgIHJldHVybjtcbiAgICB9XG5cbiAgICB2YXIgY2xhc3NOYW1lID0gdGhpcy5wcm9wcy5uYW1lW2FuaW1hdGlvblR5cGVdIHx8IHRoaXMucHJvcHMubmFtZSArICctJyArIGFuaW1hdGlvblR5cGU7XG4gICAgdmFyIGFjdGl2ZUNsYXNzTmFtZSA9IHRoaXMucHJvcHMubmFtZVthbmltYXRpb25UeXBlICsgJ0FjdGl2ZSddIHx8IGNsYXNzTmFtZSArICctYWN0aXZlJztcbiAgICB2YXIgdGltZXIgPSBudWxsO1xuICAgIHZhciByZW1vdmVMaXN0ZW5lcnMgPSB2b2lkIDA7XG5cbiAgICAoMCwgX2FkZENsYXNzMi5kZWZhdWx0KShub2RlLCBjbGFzc05hbWUpO1xuXG4gICAgLy8gTmVlZCB0byBkbyB0aGlzIHRvIGFjdHVhbGx5IHRyaWdnZXIgYSB0cmFuc2l0aW9uLlxuICAgIHRoaXMucXVldWVDbGFzc0FuZE5vZGUoYWN0aXZlQ2xhc3NOYW1lLCBub2RlKTtcblxuICAgIC8vIENsZWFuLXVwIHRoZSBhbmltYXRpb24gYWZ0ZXIgdGhlIHNwZWNpZmllZCBkZWxheVxuICAgIHZhciBmaW5pc2ggPSBmdW5jdGlvbiBmaW5pc2goZSkge1xuICAgICAgaWYgKGUgJiYgZS50YXJnZXQgIT09IG5vZGUpIHtcbiAgICAgICAgcmV0dXJuO1xuICAgICAgfVxuXG4gICAgICBjbGVhclRpbWVvdXQodGltZXIpO1xuICAgICAgaWYgKHJlbW92ZUxpc3RlbmVycykgcmVtb3ZlTGlzdGVuZXJzKCk7XG5cbiAgICAgICgwLCBfcmVtb3ZlQ2xhc3MyLmRlZmF1bHQpKG5vZGUsIGNsYXNzTmFtZSk7XG4gICAgICAoMCwgX3JlbW92ZUNsYXNzMi5kZWZhdWx0KShub2RlLCBhY3RpdmVDbGFzc05hbWUpO1xuXG4gICAgICBpZiAocmVtb3ZlTGlzdGVuZXJzKSByZW1vdmVMaXN0ZW5lcnMoKTtcblxuICAgICAgLy8gVXN1YWxseSB0aGlzIG9wdGlvbmFsIGNhbGxiYWNrIGlzIHVzZWQgZm9yIGluZm9ybWluZyBhbiBvd25lciBvZlxuICAgICAgLy8gYSBsZWF2ZSBhbmltYXRpb24gYW5kIHRlbGxpbmcgaXQgdG8gcmVtb3ZlIHRoZSBjaGlsZC5cbiAgICAgIGlmIChmaW5pc2hDYWxsYmFjaykge1xuICAgICAgICBmaW5pc2hDYWxsYmFjaygpO1xuICAgICAgfVxuICAgIH07XG5cbiAgICBpZiAodGltZW91dCkge1xuICAgICAgdGltZXIgPSBzZXRUaW1lb3V0KGZpbmlzaCwgdGltZW91dCk7XG4gICAgICB0aGlzLnRyYW5zaXRpb25UaW1lb3V0cy5wdXNoKHRpbWVyKTtcbiAgICB9IGVsc2UgaWYgKF9wcm9wZXJ0aWVzLnRyYW5zaXRpb25FbmQpIHtcbiAgICAgIHJlbW92ZUxpc3RlbmVycyA9IGFkZEVuZExpc3RlbmVyKG5vZGUsIGZpbmlzaCk7XG4gICAgfVxuICB9O1xuXG4gIENTU1RyYW5zaXRpb25Hcm91cENoaWxkLnByb3RvdHlwZS5xdWV1ZUNsYXNzQW5kTm9kZSA9IGZ1bmN0aW9uIHF1ZXVlQ2xhc3NBbmROb2RlKGNsYXNzTmFtZSwgbm9kZSkge1xuICAgIHZhciBfdGhpczIgPSB0aGlzO1xuXG4gICAgdGhpcy5jbGFzc05hbWVBbmROb2RlUXVldWUucHVzaCh7XG4gICAgICBjbGFzc05hbWU6IGNsYXNzTmFtZSxcbiAgICAgIG5vZGU6IG5vZGVcbiAgICB9KTtcblxuICAgIGlmICghdGhpcy5yYWZIYW5kbGUpIHtcbiAgICAgIHRoaXMucmFmSGFuZGxlID0gKDAsIF9yZXF1ZXN0QW5pbWF0aW9uRnJhbWUyLmRlZmF1bHQpKGZ1bmN0aW9uICgpIHtcbiAgICAgICAgcmV0dXJuIF90aGlzMi5mbHVzaENsYXNzTmFtZUFuZE5vZGVRdWV1ZSgpO1xuICAgICAgfSk7XG4gICAgfVxuICB9O1xuXG4gIENTU1RyYW5zaXRpb25Hcm91cENoaWxkLnByb3RvdHlwZS5mbHVzaENsYXNzTmFtZUFuZE5vZGVRdWV1ZSA9IGZ1bmN0aW9uIGZsdXNoQ2xhc3NOYW1lQW5kTm9kZVF1ZXVlKCkge1xuICAgIGlmICghdGhpcy51bm1vdW50ZWQpIHtcbiAgICAgIHRoaXMuY2xhc3NOYW1lQW5kTm9kZVF1ZXVlLmZvckVhY2goZnVuY3Rpb24gKG9iaikge1xuICAgICAgICAvLyBUaGlzIGlzIGZvciB0byBmb3JjZSBhIHJlcGFpbnQsXG4gICAgICAgIC8vIHdoaWNoIGlzIG5lY2Vzc2FyeSBpbiBvcmRlciB0byB0cmFuc2l0aW9uIHN0eWxlcyB3aGVuIGFkZGluZyBhIGNsYXNzIG5hbWUuXG4gICAgICAgIC8qIGVzbGludC1kaXNhYmxlIG5vLXVudXNlZC1leHByZXNzaW9ucyAqL1xuICAgICAgICBvYmoubm9kZS5zY3JvbGxUb3A7XG4gICAgICAgIC8qIGVzbGludC1lbmFibGUgbm8tdW51c2VkLWV4cHJlc3Npb25zICovXG4gICAgICAgICgwLCBfYWRkQ2xhc3MyLmRlZmF1bHQpKG9iai5ub2RlLCBvYmouY2xhc3NOYW1lKTtcbiAgICAgIH0pO1xuICAgIH1cbiAgICB0aGlzLmNsYXNzTmFtZUFuZE5vZGVRdWV1ZS5sZW5ndGggPSAwO1xuICAgIHRoaXMucmFmSGFuZGxlID0gbnVsbDtcbiAgfTtcblxuICBDU1NUcmFuc2l0aW9uR3JvdXBDaGlsZC5wcm90b3R5cGUucmVuZGVyID0gZnVuY3Rpb24gcmVuZGVyKCkge1xuICAgIHZhciBwcm9wcyA9IF9leHRlbmRzKHt9LCB0aGlzLnByb3BzKTtcbiAgICBkZWxldGUgcHJvcHMubmFtZTtcbiAgICBkZWxldGUgcHJvcHMuYXBwZWFyO1xuICAgIGRlbGV0ZSBwcm9wcy5lbnRlcjtcbiAgICBkZWxldGUgcHJvcHMubGVhdmU7XG4gICAgZGVsZXRlIHByb3BzLmFwcGVhclRpbWVvdXQ7XG4gICAgZGVsZXRlIHByb3BzLmVudGVyVGltZW91dDtcbiAgICBkZWxldGUgcHJvcHMubGVhdmVUaW1lb3V0O1xuICAgIGRlbGV0ZSBwcm9wcy5jaGlsZHJlbjtcbiAgICByZXR1cm4gX3JlYWN0Mi5kZWZhdWx0LmNsb25lRWxlbWVudChfcmVhY3QyLmRlZmF1bHQuQ2hpbGRyZW4ub25seSh0aGlzLnByb3BzLmNoaWxkcmVuKSwgcHJvcHMpO1xuICB9O1xuXG4gIHJldHVybiBDU1NUcmFuc2l0aW9uR3JvdXBDaGlsZDtcbn0oX3JlYWN0Mi5kZWZhdWx0LkNvbXBvbmVudCk7XG5cbkNTU1RyYW5zaXRpb25Hcm91cENoaWxkLmRpc3BsYXlOYW1lID0gJ0NTU1RyYW5zaXRpb25Hcm91cENoaWxkJztcblxuXG5DU1NUcmFuc2l0aW9uR3JvdXBDaGlsZC5wcm9wVHlwZXMgPSBwcm9jZXNzLmVudi5OT0RFX0VOViAhPT0gXCJwcm9kdWN0aW9uXCIgPyBwcm9wVHlwZXMgOiB7fTtcblxuZXhwb3J0cy5kZWZhdWx0ID0gQ1NTVHJhbnNpdGlvbkdyb3VwQ2hpbGQ7XG5tb2R1bGUuZXhwb3J0cyA9IGV4cG9ydHNbJ2RlZmF1bHQnXTsiLCIndXNlIHN0cmljdCc7XG5cbmV4cG9ydHMuX19lc01vZHVsZSA9IHRydWU7XG5cbnZhciBfZXh0ZW5kcyA9IE9iamVjdC5hc3NpZ24gfHwgZnVuY3Rpb24gKHRhcmdldCkgeyBmb3IgKHZhciBpID0gMTsgaSA8IGFyZ3VtZW50cy5sZW5ndGg7IGkrKykgeyB2YXIgc291cmNlID0gYXJndW1lbnRzW2ldOyBmb3IgKHZhciBrZXkgaW4gc291cmNlKSB7IGlmIChPYmplY3QucHJvdG90eXBlLmhhc093blByb3BlcnR5LmNhbGwoc291cmNlLCBrZXkpKSB7IHRhcmdldFtrZXldID0gc291cmNlW2tleV07IH0gfSB9IHJldHVybiB0YXJnZXQ7IH07XG5cbnZhciBfcmVhY3QgPSByZXF1aXJlKCdyZWFjdCcpO1xuXG52YXIgX3JlYWN0MiA9IF9pbnRlcm9wUmVxdWlyZURlZmF1bHQoX3JlYWN0KTtcblxudmFyIF9wcm9wVHlwZXMgPSByZXF1aXJlKCdwcm9wLXR5cGVzJyk7XG5cbnZhciBfcHJvcFR5cGVzMiA9IF9pbnRlcm9wUmVxdWlyZURlZmF1bHQoX3Byb3BUeXBlcyk7XG5cbnZhciBfVHJhbnNpdGlvbkdyb3VwID0gcmVxdWlyZSgnLi9UcmFuc2l0aW9uR3JvdXAnKTtcblxudmFyIF9UcmFuc2l0aW9uR3JvdXAyID0gX2ludGVyb3BSZXF1aXJlRGVmYXVsdChfVHJhbnNpdGlvbkdyb3VwKTtcblxudmFyIF9DU1NUcmFuc2l0aW9uR3JvdXBDaGlsZCA9IHJlcXVpcmUoJy4vQ1NTVHJhbnNpdGlvbkdyb3VwQ2hpbGQnKTtcblxudmFyIF9DU1NUcmFuc2l0aW9uR3JvdXBDaGlsZDIgPSBfaW50ZXJvcFJlcXVpcmVEZWZhdWx0KF9DU1NUcmFuc2l0aW9uR3JvdXBDaGlsZCk7XG5cbnZhciBfUHJvcFR5cGVzID0gcmVxdWlyZSgnLi91dGlscy9Qcm9wVHlwZXMnKTtcblxuZnVuY3Rpb24gX2ludGVyb3BSZXF1aXJlRGVmYXVsdChvYmopIHsgcmV0dXJuIG9iaiAmJiBvYmouX19lc01vZHVsZSA/IG9iaiA6IHsgZGVmYXVsdDogb2JqIH07IH1cblxuZnVuY3Rpb24gX2NsYXNzQ2FsbENoZWNrKGluc3RhbmNlLCBDb25zdHJ1Y3RvcikgeyBpZiAoIShpbnN0YW5jZSBpbnN0YW5jZW9mIENvbnN0cnVjdG9yKSkgeyB0aHJvdyBuZXcgVHlwZUVycm9yKFwiQ2Fubm90IGNhbGwgYSBjbGFzcyBhcyBhIGZ1bmN0aW9uXCIpOyB9IH1cblxuZnVuY3Rpb24gX3Bvc3NpYmxlQ29uc3RydWN0b3JSZXR1cm4oc2VsZiwgY2FsbCkgeyBpZiAoIXNlbGYpIHsgdGhyb3cgbmV3IFJlZmVyZW5jZUVycm9yKFwidGhpcyBoYXNuJ3QgYmVlbiBpbml0aWFsaXNlZCAtIHN1cGVyKCkgaGFzbid0IGJlZW4gY2FsbGVkXCIpOyB9IHJldHVybiBjYWxsICYmICh0eXBlb2YgY2FsbCA9PT0gXCJvYmplY3RcIiB8fCB0eXBlb2YgY2FsbCA9PT0gXCJmdW5jdGlvblwiKSA/IGNhbGwgOiBzZWxmOyB9XG5cbmZ1bmN0aW9uIF9pbmhlcml0cyhzdWJDbGFzcywgc3VwZXJDbGFzcykgeyBpZiAodHlwZW9mIHN1cGVyQ2xhc3MgIT09IFwiZnVuY3Rpb25cIiAmJiBzdXBlckNsYXNzICE9PSBudWxsKSB7IHRocm93IG5ldyBUeXBlRXJyb3IoXCJTdXBlciBleHByZXNzaW9uIG11c3QgZWl0aGVyIGJlIG51bGwgb3IgYSBmdW5jdGlvbiwgbm90IFwiICsgdHlwZW9mIHN1cGVyQ2xhc3MpOyB9IHN1YkNsYXNzLnByb3RvdHlwZSA9IE9iamVjdC5jcmVhdGUoc3VwZXJDbGFzcyAmJiBzdXBlckNsYXNzLnByb3RvdHlwZSwgeyBjb25zdHJ1Y3RvcjogeyB2YWx1ZTogc3ViQ2xhc3MsIGVudW1lcmFibGU6IGZhbHNlLCB3cml0YWJsZTogdHJ1ZSwgY29uZmlndXJhYmxlOiB0cnVlIH0gfSk7IGlmIChzdXBlckNsYXNzKSBPYmplY3Quc2V0UHJvdG90eXBlT2YgPyBPYmplY3Quc2V0UHJvdG90eXBlT2Yoc3ViQ2xhc3MsIHN1cGVyQ2xhc3MpIDogc3ViQ2xhc3MuX19wcm90b19fID0gc3VwZXJDbGFzczsgfVxuXG52YXIgcHJvcFR5cGVzID0ge1xuICB0cmFuc2l0aW9uTmFtZTogX1Byb3BUeXBlcy5uYW1lU2hhcGUuaXNSZXF1aXJlZCxcblxuICB0cmFuc2l0aW9uQXBwZWFyOiBfcHJvcFR5cGVzMi5kZWZhdWx0LmJvb2wsXG4gIHRyYW5zaXRpb25FbnRlcjogX3Byb3BUeXBlczIuZGVmYXVsdC5ib29sLFxuICB0cmFuc2l0aW9uTGVhdmU6IF9wcm9wVHlwZXMyLmRlZmF1bHQuYm9vbCxcbiAgdHJhbnNpdGlvbkFwcGVhclRpbWVvdXQ6ICgwLCBfUHJvcFR5cGVzLnRyYW5zaXRpb25UaW1lb3V0KSgnQXBwZWFyJyksXG4gIHRyYW5zaXRpb25FbnRlclRpbWVvdXQ6ICgwLCBfUHJvcFR5cGVzLnRyYW5zaXRpb25UaW1lb3V0KSgnRW50ZXInKSxcbiAgdHJhbnNpdGlvbkxlYXZlVGltZW91dDogKDAsIF9Qcm9wVHlwZXMudHJhbnNpdGlvblRpbWVvdXQpKCdMZWF2ZScpXG59O1xuXG52YXIgZGVmYXVsdFByb3BzID0ge1xuICB0cmFuc2l0aW9uQXBwZWFyOiBmYWxzZSxcbiAgdHJhbnNpdGlvbkVudGVyOiB0cnVlLFxuICB0cmFuc2l0aW9uTGVhdmU6IHRydWVcbn07XG5cbnZhciBDU1NUcmFuc2l0aW9uR3JvdXAgPSBmdW5jdGlvbiAoX1JlYWN0JENvbXBvbmVudCkge1xuICBfaW5oZXJpdHMoQ1NTVHJhbnNpdGlvbkdyb3VwLCBfUmVhY3QkQ29tcG9uZW50KTtcblxuICBmdW5jdGlvbiBDU1NUcmFuc2l0aW9uR3JvdXAoKSB7XG4gICAgdmFyIF90ZW1wLCBfdGhpcywgX3JldDtcblxuICAgIF9jbGFzc0NhbGxDaGVjayh0aGlzLCBDU1NUcmFuc2l0aW9uR3JvdXApO1xuXG4gICAgZm9yICh2YXIgX2xlbiA9IGFyZ3VtZW50cy5sZW5ndGgsIGFyZ3MgPSBBcnJheShfbGVuKSwgX2tleSA9IDA7IF9rZXkgPCBfbGVuOyBfa2V5KyspIHtcbiAgICAgIGFyZ3NbX2tleV0gPSBhcmd1bWVudHNbX2tleV07XG4gICAgfVxuXG4gICAgcmV0dXJuIF9yZXQgPSAoX3RlbXAgPSAoX3RoaXMgPSBfcG9zc2libGVDb25zdHJ1Y3RvclJldHVybih0aGlzLCBfUmVhY3QkQ29tcG9uZW50LmNhbGwuYXBwbHkoX1JlYWN0JENvbXBvbmVudCwgW3RoaXNdLmNvbmNhdChhcmdzKSkpLCBfdGhpcyksIF90aGlzLl93cmFwQ2hpbGQgPSBmdW5jdGlvbiAoY2hpbGQpIHtcbiAgICAgIHJldHVybiBfcmVhY3QyLmRlZmF1bHQuY3JlYXRlRWxlbWVudChfQ1NTVHJhbnNpdGlvbkdyb3VwQ2hpbGQyLmRlZmF1bHQsIHtcbiAgICAgICAgbmFtZTogX3RoaXMucHJvcHMudHJhbnNpdGlvbk5hbWUsXG4gICAgICAgIGFwcGVhcjogX3RoaXMucHJvcHMudHJhbnNpdGlvbkFwcGVhcixcbiAgICAgICAgZW50ZXI6IF90aGlzLnByb3BzLnRyYW5zaXRpb25FbnRlcixcbiAgICAgICAgbGVhdmU6IF90aGlzLnByb3BzLnRyYW5zaXRpb25MZWF2ZSxcbiAgICAgICAgYXBwZWFyVGltZW91dDogX3RoaXMucHJvcHMudHJhbnNpdGlvbkFwcGVhclRpbWVvdXQsXG4gICAgICAgIGVudGVyVGltZW91dDogX3RoaXMucHJvcHMudHJhbnNpdGlvbkVudGVyVGltZW91dCxcbiAgICAgICAgbGVhdmVUaW1lb3V0OiBfdGhpcy5wcm9wcy50cmFuc2l0aW9uTGVhdmVUaW1lb3V0XG4gICAgICB9LCBjaGlsZCk7XG4gICAgfSwgX3RlbXApLCBfcG9zc2libGVDb25zdHJ1Y3RvclJldHVybihfdGhpcywgX3JldCk7XG4gIH1cblxuICAvLyBXZSBuZWVkIHRvIHByb3ZpZGUgdGhpcyBjaGlsZEZhY3Rvcnkgc28gdGhhdFxuICAvLyBSZWFjdENTU1RyYW5zaXRpb25Hcm91cENoaWxkIGNhbiByZWNlaXZlIHVwZGF0ZXMgdG8gbmFtZSwgZW50ZXIsIGFuZFxuICAvLyBsZWF2ZSB3aGlsZSBpdCBpcyBsZWF2aW5nLlxuXG5cbiAgQ1NTVHJhbnNpdGlvbkdyb3VwLnByb3RvdHlwZS5yZW5kZXIgPSBmdW5jdGlvbiByZW5kZXIoKSB7XG4gICAgcmV0dXJuIF9yZWFjdDIuZGVmYXVsdC5jcmVhdGVFbGVtZW50KF9UcmFuc2l0aW9uR3JvdXAyLmRlZmF1bHQsIF9leHRlbmRzKHt9LCB0aGlzLnByb3BzLCB7IGNoaWxkRmFjdG9yeTogdGhpcy5fd3JhcENoaWxkIH0pKTtcbiAgfTtcblxuICByZXR1cm4gQ1NTVHJhbnNpdGlvbkdyb3VwO1xufShfcmVhY3QyLmRlZmF1bHQuQ29tcG9uZW50KTtcblxuQ1NTVHJhbnNpdGlvbkdyb3VwLmRpc3BsYXlOYW1lID0gJ0NTU1RyYW5zaXRpb25Hcm91cCc7XG5cblxuQ1NTVHJhbnNpdGlvbkdyb3VwLnByb3BUeXBlcyA9IHByb2Nlc3MuZW52Lk5PREVfRU5WICE9PSBcInByb2R1Y3Rpb25cIiA/IHByb3BUeXBlcyA6IHt9O1xuQ1NTVHJhbnNpdGlvbkdyb3VwLmRlZmF1bHRQcm9wcyA9IGRlZmF1bHRQcm9wcztcblxuZXhwb3J0cy5kZWZhdWx0ID0gQ1NTVHJhbnNpdGlvbkdyb3VwO1xubW9kdWxlLmV4cG9ydHMgPSBleHBvcnRzWydkZWZhdWx0J107IiwiJ3VzZSBzdHJpY3QnO1xuXG52YXIgX0NTU1RyYW5zaXRpb25Hcm91cCA9IHJlcXVpcmUoJy4vQ1NTVHJhbnNpdGlvbkdyb3VwJyk7XG5cbnZhciBfQ1NTVHJhbnNpdGlvbkdyb3VwMiA9IF9pbnRlcm9wUmVxdWlyZURlZmF1bHQoX0NTU1RyYW5zaXRpb25Hcm91cCk7XG5cbnZhciBfVHJhbnNpdGlvbkdyb3VwID0gcmVxdWlyZSgnLi9UcmFuc2l0aW9uR3JvdXAnKTtcblxudmFyIF9UcmFuc2l0aW9uR3JvdXAyID0gX2ludGVyb3BSZXF1aXJlRGVmYXVsdChfVHJhbnNpdGlvbkdyb3VwKTtcblxuZnVuY3Rpb24gX2ludGVyb3BSZXF1aXJlRGVmYXVsdChvYmopIHsgcmV0dXJuIG9iaiAmJiBvYmouX19lc01vZHVsZSA/IG9iaiA6IHsgZGVmYXVsdDogb2JqIH07IH1cblxubW9kdWxlLmV4cG9ydHMgPSB7XG4gIFRyYW5zaXRpb25Hcm91cDogX1RyYW5zaXRpb25Hcm91cDIuZGVmYXVsdCxcbiAgQ1NTVHJhbnNpdGlvbkdyb3VwOiBfQ1NTVHJhbnNpdGlvbkdyb3VwMi5kZWZhdWx0XG59OyIsImltcG9ydCBSZWFjdCBmcm9tICdyZWFjdCc7XG5pbXBvcnQgeyBUcmFuc2l0aW9uR3JvdXAgfSBmcm9tICdAYmtyZW0vcmVhY3QtdHJhbnNpdGlvbi1ncm91cCc7XG5jb25zdCBUcmFuc2l0aW9uR3JvdXBXcmFwcGVyID0gKHByb3BzKSA9PiBwcm9wcy5lbmFibGVMZWdhY3lUcmFuc2l0aW9ucyA/IChSZWFjdC5jcmVhdGVFbGVtZW50KFRyYW5zaXRpb25Hcm91cCwgeyBjb21wb25lbnQ6IHByb3BzLmNvbXBvbmVudCwgY2xhc3NOYW1lOiBwcm9wcy5jbGFzc05hbWUsIHRyYW5zZm9ybTogcHJvcHMudHJhbnNmb3JtIH0sIHByb3BzLmNoaWxkcmVuKSkgOiAoUmVhY3QuY3JlYXRlRWxlbWVudChcImdcIiwgeyBjbGFzc05hbWU6IHByb3BzLmNsYXNzTmFtZSwgdHJhbnNmb3JtOiBwcm9wcy50cmFuc2Zvcm0gfSwgcHJvcHMuY2hpbGRyZW4pKTtcbmV4cG9ydCBkZWZhdWx0IFRyYW5zaXRpb25Hcm91cFdyYXBwZXI7XG4iLCJpbXBvcnQgUmVhY3QgZnJvbSAncmVhY3QnO1xuY29uc3QgREVGQVVMVF9OT0RFX0NJUkNMRV9SQURJVVMgPSAxNTtcbmNvbnN0IHRleHRMYXlvdXQgPSB7XG4gICAgdGl0bGU6IHtcbiAgICAgICAgdGV4dEFuY2hvcjogJ3N0YXJ0JyxcbiAgICAgICAgeDogNDAsXG4gICAgfSxcbiAgICBhdHRyaWJ1dGU6IHtcbiAgICAgICAgeDogNDAsXG4gICAgICAgIGR5OiAnMS4yZW0nLFxuICAgIH0sXG59O1xuY29uc3QgRGVmYXVsdE5vZGVFbGVtZW50ID0gKHsgbm9kZURhdHVtLCB0b2dnbGVOb2RlLCBvbk5vZGVDbGljaywgb25Ob2RlTW91c2VPdmVyLCBvbk5vZGVNb3VzZU91dCwgfSkgPT4gKFJlYWN0LmNyZWF0ZUVsZW1lbnQoUmVhY3QuRnJhZ21lbnQsIG51bGwsXG4gICAgUmVhY3QuY3JlYXRlRWxlbWVudChcImNpcmNsZVwiLCB7IHI6IERFRkFVTFRfTk9ERV9DSVJDTEVfUkFESVVTLCBvbkNsaWNrOiBldnQgPT4ge1xuICAgICAgICAgICAgdG9nZ2xlTm9kZSgpO1xuICAgICAgICAgICAgb25Ob2RlQ2xpY2soZXZ0KTtcbiAgICAgICAgfSwgb25Nb3VzZU92ZXI6IG9uTm9kZU1vdXNlT3Zlciwgb25Nb3VzZU91dDogb25Ob2RlTW91c2VPdXQgfSksXG4gICAgUmVhY3QuY3JlYXRlRWxlbWVudChcImdcIiwgeyBjbGFzc05hbWU6IFwicmQzdC1sYWJlbFwiIH0sXG4gICAgICAgIFJlYWN0LmNyZWF0ZUVsZW1lbnQoXCJ0ZXh0XCIsIE9iamVjdC5hc3NpZ24oeyBjbGFzc05hbWU6IFwicmQzdC1sYWJlbF9fdGl0bGVcIiB9LCB0ZXh0TGF5b3V0LnRpdGxlKSwgbm9kZURhdHVtLm5hbWUpLFxuICAgICAgICBSZWFjdC5jcmVhdGVFbGVtZW50KFwidGV4dFwiLCB7IGNsYXNzTmFtZTogXCJyZDN0LWxhYmVsX19hdHRyaWJ1dGVzXCIgfSwgbm9kZURhdHVtLmF0dHJpYnV0ZXMgJiZcbiAgICAgICAgICAgIE9iamVjdC5lbnRyaWVzKG5vZGVEYXR1bS5hdHRyaWJ1dGVzKS5tYXAoKFtsYWJlbEtleSwgbGFiZWxWYWx1ZV0sIGkpID0+IChSZWFjdC5jcmVhdGVFbGVtZW50KFwidHNwYW5cIiwgT2JqZWN0LmFzc2lnbih7IGtleTogYCR7bGFiZWxLZXl9LSR7aX1gIH0sIHRleHRMYXlvdXQuYXR0cmlidXRlKSxcbiAgICAgICAgICAgICAgICBsYWJlbEtleSxcbiAgICAgICAgICAgICAgICBcIjogXCIsXG4gICAgICAgICAgICAgICAgdHlwZW9mIGxhYmVsVmFsdWUgPT09ICdib29sZWFuJyA/IGxhYmVsVmFsdWUudG9TdHJpbmcoKSA6IGxhYmVsVmFsdWUpKSkpKSkpO1xuZXhwb3J0IGRlZmF1bHQgRGVmYXVsdE5vZGVFbGVtZW50O1xuIiwiaW1wb3J0IFJlYWN0IGZyb20gJ3JlYWN0JztcbmltcG9ydCB7IHNlbGVjdCB9IGZyb20gJ2QzLXNlbGVjdGlvbic7XG5pbXBvcnQgRGVmYXVsdE5vZGVFbGVtZW50IGZyb20gJy4vRGVmYXVsdE5vZGVFbGVtZW50LmpzJztcbmV4cG9ydCBkZWZhdWx0IGNsYXNzIE5vZGUgZXh0ZW5kcyBSZWFjdC5Db21wb25lbnQge1xuICAgIGNvbnN0cnVjdG9yKCkge1xuICAgICAgICBzdXBlciguLi5hcmd1bWVudHMpO1xuICAgICAgICB0aGlzLm5vZGVSZWYgPSBudWxsO1xuICAgICAgICB0aGlzLnN0YXRlID0ge1xuICAgICAgICAgICAgdHJhbnNmb3JtOiB0aGlzLnNldFRyYW5zZm9ybSh0aGlzLnByb3BzLnBvc2l0aW9uLCB0aGlzLnByb3BzLnBhcmVudCwgdGhpcy5wcm9wcy5vcmllbnRhdGlvbiwgdHJ1ZSksXG4gICAgICAgICAgICBpbml0aWFsU3R5bGU6IHtcbiAgICAgICAgICAgICAgICBvcGFjaXR5OiAwLFxuICAgICAgICAgICAgfSxcbiAgICAgICAgICAgIHdhc0NsaWNrZWQ6IGZhbHNlLFxuICAgICAgICB9O1xuICAgICAgICB0aGlzLnNob3VsZE5vZGVUcmFuc2Zvcm0gPSAob3duUHJvcHMsIG5leHRQcm9wcywgb3duU3RhdGUsIG5leHRTdGF0ZSkgPT4gbmV4dFByb3BzLnN1YnNjcmlwdGlvbnMgIT09IG93blByb3BzLnN1YnNjcmlwdGlvbnMgfHxcbiAgICAgICAgICAgIG5leHRQcm9wcy5wb3NpdGlvbi54ICE9PSBvd25Qcm9wcy5wb3NpdGlvbi54IHx8XG4gICAgICAgICAgICBuZXh0UHJvcHMucG9zaXRpb24ueSAhPT0gb3duUHJvcHMucG9zaXRpb24ueSB8fFxuICAgICAgICAgICAgbmV4dFByb3BzLm9yaWVudGF0aW9uICE9PSBvd25Qcm9wcy5vcmllbnRhdGlvbiB8fFxuICAgICAgICAgICAgbmV4dFN0YXRlLndhc0NsaWNrZWQgIT09IG93blN0YXRlLndhc0NsaWNrZWQ7XG4gICAgICAgIC8vIFRPRE86IG5lZWRzIHRlc3RzXG4gICAgICAgIHRoaXMucmVuZGVyTm9kZUVsZW1lbnQgPSAoKSA9PiB7XG4gICAgICAgICAgICBjb25zdCB7IGRhdGEsIGhpZXJhcmNoeVBvaW50Tm9kZSwgcmVuZGVyQ3VzdG9tTm9kZUVsZW1lbnQgfSA9IHRoaXMucHJvcHM7XG4gICAgICAgICAgICBjb25zdCByZW5kZXJOb2RlID0gdHlwZW9mIHJlbmRlckN1c3RvbU5vZGVFbGVtZW50ID09PSAnZnVuY3Rpb24nID8gcmVuZGVyQ3VzdG9tTm9kZUVsZW1lbnQgOiBEZWZhdWx0Tm9kZUVsZW1lbnQ7XG4gICAgICAgICAgICBjb25zdCBub2RlUHJvcHMgPSB7XG4gICAgICAgICAgICAgICAgaGllcmFyY2h5UG9pbnROb2RlOiBoaWVyYXJjaHlQb2ludE5vZGUsXG4gICAgICAgICAgICAgICAgbm9kZURhdHVtOiBkYXRhLFxuICAgICAgICAgICAgICAgIHRvZ2dsZU5vZGU6IHRoaXMuaGFuZGxlTm9kZVRvZ2dsZSxcbiAgICAgICAgICAgICAgICBvbk5vZGVDbGljazogdGhpcy5oYW5kbGVPbkNsaWNrLFxuICAgICAgICAgICAgICAgIG9uTm9kZU1vdXNlT3ZlcjogdGhpcy5oYW5kbGVPbk1vdXNlT3ZlcixcbiAgICAgICAgICAgICAgICBvbk5vZGVNb3VzZU91dDogdGhpcy5oYW5kbGVPbk1vdXNlT3V0LFxuICAgICAgICAgICAgICAgIGFkZENoaWxkcmVuOiB0aGlzLmhhbmRsZUFkZENoaWxkcmVuLFxuICAgICAgICAgICAgfTtcbiAgICAgICAgICAgIHJldHVybiByZW5kZXJOb2RlKG5vZGVQcm9wcyk7XG4gICAgICAgIH07XG4gICAgICAgIHRoaXMuaGFuZGxlTm9kZVRvZ2dsZSA9ICgpID0+IHtcbiAgICAgICAgICAgIHRoaXMuc2V0U3RhdGUoeyB3YXNDbGlja2VkOiB0cnVlIH0pO1xuICAgICAgICAgICAgdGhpcy5wcm9wcy5vbk5vZGVUb2dnbGUodGhpcy5wcm9wcy5kYXRhLl9fcmQzdC5pZCk7XG4gICAgICAgIH07XG4gICAgICAgIHRoaXMuaGFuZGxlT25DbGljayA9IGV2dCA9PiB7XG4gICAgICAgICAgICB0aGlzLnNldFN0YXRlKHsgd2FzQ2xpY2tlZDogdHJ1ZSB9KTtcbiAgICAgICAgICAgIHRoaXMucHJvcHMub25Ob2RlQ2xpY2sodGhpcy5wcm9wcy5oaWVyYXJjaHlQb2ludE5vZGUsIGV2dCk7XG4gICAgICAgIH07XG4gICAgICAgIHRoaXMuaGFuZGxlT25Nb3VzZU92ZXIgPSBldnQgPT4ge1xuICAgICAgICAgICAgdGhpcy5wcm9wcy5vbk5vZGVNb3VzZU92ZXIodGhpcy5wcm9wcy5oaWVyYXJjaHlQb2ludE5vZGUsIGV2dCk7XG4gICAgICAgIH07XG4gICAgICAgIHRoaXMuaGFuZGxlT25Nb3VzZU91dCA9IGV2dCA9PiB7XG4gICAgICAgICAgICB0aGlzLnByb3BzLm9uTm9kZU1vdXNlT3V0KHRoaXMucHJvcHMuaGllcmFyY2h5UG9pbnROb2RlLCBldnQpO1xuICAgICAgICB9O1xuICAgICAgICB0aGlzLmhhbmRsZUFkZENoaWxkcmVuID0gY2hpbGRyZW5EYXRhID0+IHtcbiAgICAgICAgICAgIHRoaXMucHJvcHMuaGFuZGxlQWRkQ2hpbGRyZW5Ub05vZGUodGhpcy5wcm9wcy5kYXRhLl9fcmQzdC5pZCwgY2hpbGRyZW5EYXRhKTtcbiAgICAgICAgfTtcbiAgICB9XG4gICAgY29tcG9uZW50RGlkTW91bnQoKSB7XG4gICAgICAgIHRoaXMuY29tbWl0VHJhbnNmb3JtKCk7XG4gICAgfVxuICAgIGNvbXBvbmVudERpZFVwZGF0ZSgpIHtcbiAgICAgICAgaWYgKHRoaXMuc3RhdGUud2FzQ2xpY2tlZCkge1xuICAgICAgICAgICAgdGhpcy5wcm9wcy5jZW50ZXJOb2RlKHRoaXMucHJvcHMuaGllcmFyY2h5UG9pbnROb2RlKTtcbiAgICAgICAgICAgIHRoaXMuc2V0U3RhdGUoeyB3YXNDbGlja2VkOiBmYWxzZSB9KTtcbiAgICAgICAgfVxuICAgICAgICB0aGlzLmNvbW1pdFRyYW5zZm9ybSgpO1xuICAgIH1cbiAgICBzaG91bGRDb21wb25lbnRVcGRhdGUobmV4dFByb3BzLCBuZXh0U3RhdGUpIHtcbiAgICAgICAgcmV0dXJuIHRoaXMuc2hvdWxkTm9kZVRyYW5zZm9ybSh0aGlzLnByb3BzLCBuZXh0UHJvcHMsIHRoaXMuc3RhdGUsIG5leHRTdGF0ZSk7XG4gICAgfVxuICAgIHNldFRyYW5zZm9ybShwb3NpdGlvbiwgcGFyZW50LCBvcmllbnRhdGlvbiwgc2hvdWxkVHJhbnNsYXRlVG9PcmlnaW4gPSBmYWxzZSkge1xuICAgICAgICBpZiAoc2hvdWxkVHJhbnNsYXRlVG9PcmlnaW4pIHtcbiAgICAgICAgICAgIGNvbnN0IGhhc1BhcmVudCA9IHBhcmVudCAhPT0gbnVsbCAmJiBwYXJlbnQgIT09IHVuZGVmaW5lZDtcbiAgICAgICAgICAgIGNvbnN0IG9yaWdpblggPSBoYXNQYXJlbnQgPyBwYXJlbnQueCA6IDA7XG4gICAgICAgICAgICBjb25zdCBvcmlnaW5ZID0gaGFzUGFyZW50ID8gcGFyZW50LnkgOiAwO1xuICAgICAgICAgICAgcmV0dXJuIG9yaWVudGF0aW9uID09PSAnaG9yaXpvbnRhbCdcbiAgICAgICAgICAgICAgICA/IGB0cmFuc2xhdGUoJHtvcmlnaW5ZfSwke29yaWdpblh9KWBcbiAgICAgICAgICAgICAgICA6IGB0cmFuc2xhdGUoJHtvcmlnaW5YfSwke29yaWdpbll9KWA7XG4gICAgICAgIH1cbiAgICAgICAgcmV0dXJuIG9yaWVudGF0aW9uID09PSAnaG9yaXpvbnRhbCdcbiAgICAgICAgICAgID8gYHRyYW5zbGF0ZSgke3Bvc2l0aW9uLnl9LCR7cG9zaXRpb24ueH0pYFxuICAgICAgICAgICAgOiBgdHJhbnNsYXRlKCR7cG9zaXRpb24ueH0sJHtwb3NpdGlvbi55fSlgO1xuICAgIH1cbiAgICBhcHBseVRyYW5zZm9ybSh0cmFuc2Zvcm0sIHRyYW5zaXRpb25EdXJhdGlvbiwgb3BhY2l0eSA9IDEsIGRvbmUgPSAoKSA9PiB7IH0pIHtcbiAgICAgICAgaWYgKHRoaXMucHJvcHMuZW5hYmxlTGVnYWN5VHJhbnNpdGlvbnMpIHtcbiAgICAgICAgICAgIHNlbGVjdCh0aGlzLm5vZGVSZWYpXG4gICAgICAgICAgICAgICAgLy8gQHRzLWlnbm9yZVxuICAgICAgICAgICAgICAgIC50cmFuc2l0aW9uKClcbiAgICAgICAgICAgICAgICAuZHVyYXRpb24odHJhbnNpdGlvbkR1cmF0aW9uKVxuICAgICAgICAgICAgICAgIC5hdHRyKCd0cmFuc2Zvcm0nLCB0cmFuc2Zvcm0pXG4gICAgICAgICAgICAgICAgLnN0eWxlKCdvcGFjaXR5Jywgb3BhY2l0eSlcbiAgICAgICAgICAgICAgICAub24oJ2VuZCcsIGRvbmUpO1xuICAgICAgICB9XG4gICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgc2VsZWN0KHRoaXMubm9kZVJlZilcbiAgICAgICAgICAgICAgICAuYXR0cigndHJhbnNmb3JtJywgdHJhbnNmb3JtKVxuICAgICAgICAgICAgICAgIC5zdHlsZSgnb3BhY2l0eScsIG9wYWNpdHkpO1xuICAgICAgICAgICAgZG9uZSgpO1xuICAgICAgICB9XG4gICAgfVxuICAgIGNvbW1pdFRyYW5zZm9ybSgpIHtcbiAgICAgICAgY29uc3QgeyBvcmllbnRhdGlvbiwgdHJhbnNpdGlvbkR1cmF0aW9uLCBwb3NpdGlvbiwgcGFyZW50IH0gPSB0aGlzLnByb3BzO1xuICAgICAgICBjb25zdCB0cmFuc2Zvcm0gPSB0aGlzLnNldFRyYW5zZm9ybShwb3NpdGlvbiwgcGFyZW50LCBvcmllbnRhdGlvbik7XG4gICAgICAgIHRoaXMuYXBwbHlUcmFuc2Zvcm0odHJhbnNmb3JtLCB0cmFuc2l0aW9uRHVyYXRpb24pO1xuICAgIH1cbiAgICBjb21wb25lbnRXaWxsTGVhdmUoZG9uZSkge1xuICAgICAgICBjb25zdCB7IG9yaWVudGF0aW9uLCB0cmFuc2l0aW9uRHVyYXRpb24sIHBvc2l0aW9uLCBwYXJlbnQgfSA9IHRoaXMucHJvcHM7XG4gICAgICAgIGNvbnN0IHRyYW5zZm9ybSA9IHRoaXMuc2V0VHJhbnNmb3JtKHBvc2l0aW9uLCBwYXJlbnQsIG9yaWVudGF0aW9uLCB0cnVlKTtcbiAgICAgICAgdGhpcy5hcHBseVRyYW5zZm9ybSh0cmFuc2Zvcm0sIHRyYW5zaXRpb25EdXJhdGlvbiwgMCwgZG9uZSk7XG4gICAgfVxuICAgIHJlbmRlcigpIHtcbiAgICAgICAgY29uc3QgeyBkYXRhLCBub2RlQ2xhc3NOYW1lIH0gPSB0aGlzLnByb3BzO1xuICAgICAgICByZXR1cm4gKFJlYWN0LmNyZWF0ZUVsZW1lbnQoXCJnXCIsIHsgaWQ6IGRhdGEuX19yZDN0LmlkLCByZWY6IG4gPT4ge1xuICAgICAgICAgICAgICAgIHRoaXMubm9kZVJlZiA9IG47XG4gICAgICAgICAgICB9LCBzdHlsZTogdGhpcy5zdGF0ZS5pbml0aWFsU3R5bGUsIGNsYXNzTmFtZTogW1xuICAgICAgICAgICAgICAgIGRhdGEuY2hpbGRyZW4gJiYgZGF0YS5jaGlsZHJlbi5sZW5ndGggPiAwID8gJ3JkM3Qtbm9kZScgOiAncmQzdC1sZWFmLW5vZGUnLFxuICAgICAgICAgICAgICAgIG5vZGVDbGFzc05hbWUsXG4gICAgICAgICAgICBdXG4gICAgICAgICAgICAgICAgLmpvaW4oJyAnKVxuICAgICAgICAgICAgICAgIC50cmltKCksIHRyYW5zZm9ybTogdGhpcy5zdGF0ZS50cmFuc2Zvcm0gfSwgdGhpcy5yZW5kZXJOb2RlRWxlbWVudCgpKSk7XG4gICAgfVxufVxuIiwidmFyIHBpID0gTWF0aC5QSSxcbiAgICB0YXUgPSAyICogcGksXG4gICAgZXBzaWxvbiA9IDFlLTYsXG4gICAgdGF1RXBzaWxvbiA9IHRhdSAtIGVwc2lsb247XG5cbmZ1bmN0aW9uIFBhdGgoKSB7XG4gIHRoaXMuX3gwID0gdGhpcy5feTAgPSAvLyBzdGFydCBvZiBjdXJyZW50IHN1YnBhdGhcbiAgdGhpcy5feDEgPSB0aGlzLl95MSA9IG51bGw7IC8vIGVuZCBvZiBjdXJyZW50IHN1YnBhdGhcbiAgdGhpcy5fID0gXCJcIjtcbn1cblxuZnVuY3Rpb24gcGF0aCgpIHtcbiAgcmV0dXJuIG5ldyBQYXRoO1xufVxuXG5QYXRoLnByb3RvdHlwZSA9IHBhdGgucHJvdG90eXBlID0ge1xuICBjb25zdHJ1Y3RvcjogUGF0aCxcbiAgbW92ZVRvOiBmdW5jdGlvbih4LCB5KSB7XG4gICAgdGhpcy5fICs9IFwiTVwiICsgKHRoaXMuX3gwID0gdGhpcy5feDEgPSAreCkgKyBcIixcIiArICh0aGlzLl95MCA9IHRoaXMuX3kxID0gK3kpO1xuICB9LFxuICBjbG9zZVBhdGg6IGZ1bmN0aW9uKCkge1xuICAgIGlmICh0aGlzLl94MSAhPT0gbnVsbCkge1xuICAgICAgdGhpcy5feDEgPSB0aGlzLl94MCwgdGhpcy5feTEgPSB0aGlzLl95MDtcbiAgICAgIHRoaXMuXyArPSBcIlpcIjtcbiAgICB9XG4gIH0sXG4gIGxpbmVUbzogZnVuY3Rpb24oeCwgeSkge1xuICAgIHRoaXMuXyArPSBcIkxcIiArICh0aGlzLl94MSA9ICt4KSArIFwiLFwiICsgKHRoaXMuX3kxID0gK3kpO1xuICB9LFxuICBxdWFkcmF0aWNDdXJ2ZVRvOiBmdW5jdGlvbih4MSwgeTEsIHgsIHkpIHtcbiAgICB0aGlzLl8gKz0gXCJRXCIgKyAoK3gxKSArIFwiLFwiICsgKCt5MSkgKyBcIixcIiArICh0aGlzLl94MSA9ICt4KSArIFwiLFwiICsgKHRoaXMuX3kxID0gK3kpO1xuICB9LFxuICBiZXppZXJDdXJ2ZVRvOiBmdW5jdGlvbih4MSwgeTEsIHgyLCB5MiwgeCwgeSkge1xuICAgIHRoaXMuXyArPSBcIkNcIiArICgreDEpICsgXCIsXCIgKyAoK3kxKSArIFwiLFwiICsgKCt4MikgKyBcIixcIiArICgreTIpICsgXCIsXCIgKyAodGhpcy5feDEgPSAreCkgKyBcIixcIiArICh0aGlzLl95MSA9ICt5KTtcbiAgfSxcbiAgYXJjVG86IGZ1bmN0aW9uKHgxLCB5MSwgeDIsIHkyLCByKSB7XG4gICAgeDEgPSAreDEsIHkxID0gK3kxLCB4MiA9ICt4MiwgeTIgPSAreTIsIHIgPSArcjtcbiAgICB2YXIgeDAgPSB0aGlzLl94MSxcbiAgICAgICAgeTAgPSB0aGlzLl95MSxcbiAgICAgICAgeDIxID0geDIgLSB4MSxcbiAgICAgICAgeTIxID0geTIgLSB5MSxcbiAgICAgICAgeDAxID0geDAgLSB4MSxcbiAgICAgICAgeTAxID0geTAgLSB5MSxcbiAgICAgICAgbDAxXzIgPSB4MDEgKiB4MDEgKyB5MDEgKiB5MDE7XG5cbiAgICAvLyBJcyB0aGUgcmFkaXVzIG5lZ2F0aXZlPyBFcnJvci5cbiAgICBpZiAociA8IDApIHRocm93IG5ldyBFcnJvcihcIm5lZ2F0aXZlIHJhZGl1czogXCIgKyByKTtcblxuICAgIC8vIElzIHRoaXMgcGF0aCBlbXB0eT8gTW92ZSB0byAoeDEseTEpLlxuICAgIGlmICh0aGlzLl94MSA9PT0gbnVsbCkge1xuICAgICAgdGhpcy5fICs9IFwiTVwiICsgKHRoaXMuX3gxID0geDEpICsgXCIsXCIgKyAodGhpcy5feTEgPSB5MSk7XG4gICAgfVxuXG4gICAgLy8gT3IsIGlzICh4MSx5MSkgY29pbmNpZGVudCB3aXRoICh4MCx5MCk/IERvIG5vdGhpbmcuXG4gICAgZWxzZSBpZiAoIShsMDFfMiA+IGVwc2lsb24pKTtcblxuICAgIC8vIE9yLCBhcmUgKHgwLHkwKSwgKHgxLHkxKSBhbmQgKHgyLHkyKSBjb2xsaW5lYXI/XG4gICAgLy8gRXF1aXZhbGVudGx5LCBpcyAoeDEseTEpIGNvaW5jaWRlbnQgd2l0aCAoeDIseTIpP1xuICAgIC8vIE9yLCBpcyB0aGUgcmFkaXVzIHplcm8/IExpbmUgdG8gKHgxLHkxKS5cbiAgICBlbHNlIGlmICghKE1hdGguYWJzKHkwMSAqIHgyMSAtIHkyMSAqIHgwMSkgPiBlcHNpbG9uKSB8fCAhcikge1xuICAgICAgdGhpcy5fICs9IFwiTFwiICsgKHRoaXMuX3gxID0geDEpICsgXCIsXCIgKyAodGhpcy5feTEgPSB5MSk7XG4gICAgfVxuXG4gICAgLy8gT3RoZXJ3aXNlLCBkcmF3IGFuIGFyYyFcbiAgICBlbHNlIHtcbiAgICAgIHZhciB4MjAgPSB4MiAtIHgwLFxuICAgICAgICAgIHkyMCA9IHkyIC0geTAsXG4gICAgICAgICAgbDIxXzIgPSB4MjEgKiB4MjEgKyB5MjEgKiB5MjEsXG4gICAgICAgICAgbDIwXzIgPSB4MjAgKiB4MjAgKyB5MjAgKiB5MjAsXG4gICAgICAgICAgbDIxID0gTWF0aC5zcXJ0KGwyMV8yKSxcbiAgICAgICAgICBsMDEgPSBNYXRoLnNxcnQobDAxXzIpLFxuICAgICAgICAgIGwgPSByICogTWF0aC50YW4oKHBpIC0gTWF0aC5hY29zKChsMjFfMiArIGwwMV8yIC0gbDIwXzIpIC8gKDIgKiBsMjEgKiBsMDEpKSkgLyAyKSxcbiAgICAgICAgICB0MDEgPSBsIC8gbDAxLFxuICAgICAgICAgIHQyMSA9IGwgLyBsMjE7XG5cbiAgICAgIC8vIElmIHRoZSBzdGFydCB0YW5nZW50IGlzIG5vdCBjb2luY2lkZW50IHdpdGggKHgwLHkwKSwgbGluZSB0by5cbiAgICAgIGlmIChNYXRoLmFicyh0MDEgLSAxKSA+IGVwc2lsb24pIHtcbiAgICAgICAgdGhpcy5fICs9IFwiTFwiICsgKHgxICsgdDAxICogeDAxKSArIFwiLFwiICsgKHkxICsgdDAxICogeTAxKTtcbiAgICAgIH1cblxuICAgICAgdGhpcy5fICs9IFwiQVwiICsgciArIFwiLFwiICsgciArIFwiLDAsMCxcIiArICgrKHkwMSAqIHgyMCA+IHgwMSAqIHkyMCkpICsgXCIsXCIgKyAodGhpcy5feDEgPSB4MSArIHQyMSAqIHgyMSkgKyBcIixcIiArICh0aGlzLl95MSA9IHkxICsgdDIxICogeTIxKTtcbiAgICB9XG4gIH0sXG4gIGFyYzogZnVuY3Rpb24oeCwgeSwgciwgYTAsIGExLCBjY3cpIHtcbiAgICB4ID0gK3gsIHkgPSAreSwgciA9ICtyLCBjY3cgPSAhIWNjdztcbiAgICB2YXIgZHggPSByICogTWF0aC5jb3MoYTApLFxuICAgICAgICBkeSA9IHIgKiBNYXRoLnNpbihhMCksXG4gICAgICAgIHgwID0geCArIGR4LFxuICAgICAgICB5MCA9IHkgKyBkeSxcbiAgICAgICAgY3cgPSAxIF4gY2N3LFxuICAgICAgICBkYSA9IGNjdyA/IGEwIC0gYTEgOiBhMSAtIGEwO1xuXG4gICAgLy8gSXMgdGhlIHJhZGl1cyBuZWdhdGl2ZT8gRXJyb3IuXG4gICAgaWYgKHIgPCAwKSB0aHJvdyBuZXcgRXJyb3IoXCJuZWdhdGl2ZSByYWRpdXM6IFwiICsgcik7XG5cbiAgICAvLyBJcyB0aGlzIHBhdGggZW1wdHk/IE1vdmUgdG8gKHgwLHkwKS5cbiAgICBpZiAodGhpcy5feDEgPT09IG51bGwpIHtcbiAgICAgIHRoaXMuXyArPSBcIk1cIiArIHgwICsgXCIsXCIgKyB5MDtcbiAgICB9XG5cbiAgICAvLyBPciwgaXMgKHgwLHkwKSBub3QgY29pbmNpZGVudCB3aXRoIHRoZSBwcmV2aW91cyBwb2ludD8gTGluZSB0byAoeDAseTApLlxuICAgIGVsc2UgaWYgKE1hdGguYWJzKHRoaXMuX3gxIC0geDApID4gZXBzaWxvbiB8fCBNYXRoLmFicyh0aGlzLl95MSAtIHkwKSA+IGVwc2lsb24pIHtcbiAgICAgIHRoaXMuXyArPSBcIkxcIiArIHgwICsgXCIsXCIgKyB5MDtcbiAgICB9XG5cbiAgICAvLyBJcyB0aGlzIGFyYyBlbXB0eT8gV2XigJlyZSBkb25lLlxuICAgIGlmICghcikgcmV0dXJuO1xuXG4gICAgLy8gRG9lcyB0aGUgYW5nbGUgZ28gdGhlIHdyb25nIHdheT8gRmxpcCB0aGUgZGlyZWN0aW9uLlxuICAgIGlmIChkYSA8IDApIGRhID0gZGEgJSB0YXUgKyB0YXU7XG5cbiAgICAvLyBJcyB0aGlzIGEgY29tcGxldGUgY2lyY2xlPyBEcmF3IHR3byBhcmNzIHRvIGNvbXBsZXRlIHRoZSBjaXJjbGUuXG4gICAgaWYgKGRhID4gdGF1RXBzaWxvbikge1xuICAgICAgdGhpcy5fICs9IFwiQVwiICsgciArIFwiLFwiICsgciArIFwiLDAsMSxcIiArIGN3ICsgXCIsXCIgKyAoeCAtIGR4KSArIFwiLFwiICsgKHkgLSBkeSkgKyBcIkFcIiArIHIgKyBcIixcIiArIHIgKyBcIiwwLDEsXCIgKyBjdyArIFwiLFwiICsgKHRoaXMuX3gxID0geDApICsgXCIsXCIgKyAodGhpcy5feTEgPSB5MCk7XG4gICAgfVxuXG4gICAgLy8gSXMgdGhpcyBhcmMgbm9uLWVtcHR5PyBEcmF3IGFuIGFyYyFcbiAgICBlbHNlIGlmIChkYSA+IGVwc2lsb24pIHtcbiAgICAgIHRoaXMuXyArPSBcIkFcIiArIHIgKyBcIixcIiArIHIgKyBcIiwwLFwiICsgKCsoZGEgPj0gcGkpKSArIFwiLFwiICsgY3cgKyBcIixcIiArICh0aGlzLl94MSA9IHggKyByICogTWF0aC5jb3MoYTEpKSArIFwiLFwiICsgKHRoaXMuX3kxID0geSArIHIgKiBNYXRoLnNpbihhMSkpO1xuICAgIH1cbiAgfSxcbiAgcmVjdDogZnVuY3Rpb24oeCwgeSwgdywgaCkge1xuICAgIHRoaXMuXyArPSBcIk1cIiArICh0aGlzLl94MCA9IHRoaXMuX3gxID0gK3gpICsgXCIsXCIgKyAodGhpcy5feTAgPSB0aGlzLl95MSA9ICt5KSArIFwiaFwiICsgKCt3KSArIFwidlwiICsgKCtoKSArIFwiaFwiICsgKC13KSArIFwiWlwiO1xuICB9LFxuICB0b1N0cmluZzogZnVuY3Rpb24oKSB7XG4gICAgcmV0dXJuIHRoaXMuXztcbiAgfVxufTtcblxuZXhwb3J0IGRlZmF1bHQgcGF0aDtcbiIsImV4cG9ydCBkZWZhdWx0IGZ1bmN0aW9uKHgpIHtcbiAgcmV0dXJuIGZ1bmN0aW9uIGNvbnN0YW50KCkge1xuICAgIHJldHVybiB4O1xuICB9O1xufVxuIiwiZXhwb3J0IGZ1bmN0aW9uIHgocCkge1xuICByZXR1cm4gcFswXTtcbn1cblxuZXhwb3J0IGZ1bmN0aW9uIHkocCkge1xuICByZXR1cm4gcFsxXTtcbn1cbiIsImV4cG9ydCB2YXIgc2xpY2UgPSBBcnJheS5wcm90b3R5cGUuc2xpY2U7XG4iLCJpbXBvcnQge3BhdGh9IGZyb20gXCJkMy1wYXRoXCI7XG5pbXBvcnQge3NsaWNlfSBmcm9tIFwiLi4vYXJyYXkuanNcIjtcbmltcG9ydCBjb25zdGFudCBmcm9tIFwiLi4vY29uc3RhbnQuanNcIjtcbmltcG9ydCB7eCBhcyBwb2ludFgsIHkgYXMgcG9pbnRZfSBmcm9tIFwiLi4vcG9pbnQuanNcIjtcbmltcG9ydCBwb2ludFJhZGlhbCBmcm9tIFwiLi4vcG9pbnRSYWRpYWwuanNcIjtcblxuZnVuY3Rpb24gbGlua1NvdXJjZShkKSB7XG4gIHJldHVybiBkLnNvdXJjZTtcbn1cblxuZnVuY3Rpb24gbGlua1RhcmdldChkKSB7XG4gIHJldHVybiBkLnRhcmdldDtcbn1cblxuZnVuY3Rpb24gbGluayhjdXJ2ZSkge1xuICB2YXIgc291cmNlID0gbGlua1NvdXJjZSxcbiAgICAgIHRhcmdldCA9IGxpbmtUYXJnZXQsXG4gICAgICB4ID0gcG9pbnRYLFxuICAgICAgeSA9IHBvaW50WSxcbiAgICAgIGNvbnRleHQgPSBudWxsO1xuXG4gIGZ1bmN0aW9uIGxpbmsoKSB7XG4gICAgdmFyIGJ1ZmZlciwgYXJndiA9IHNsaWNlLmNhbGwoYXJndW1lbnRzKSwgcyA9IHNvdXJjZS5hcHBseSh0aGlzLCBhcmd2KSwgdCA9IHRhcmdldC5hcHBseSh0aGlzLCBhcmd2KTtcbiAgICBpZiAoIWNvbnRleHQpIGNvbnRleHQgPSBidWZmZXIgPSBwYXRoKCk7XG4gICAgY3VydmUoY29udGV4dCwgK3guYXBwbHkodGhpcywgKGFyZ3ZbMF0gPSBzLCBhcmd2KSksICt5LmFwcGx5KHRoaXMsIGFyZ3YpLCAreC5hcHBseSh0aGlzLCAoYXJndlswXSA9IHQsIGFyZ3YpKSwgK3kuYXBwbHkodGhpcywgYXJndikpO1xuICAgIGlmIChidWZmZXIpIHJldHVybiBjb250ZXh0ID0gbnVsbCwgYnVmZmVyICsgXCJcIiB8fCBudWxsO1xuICB9XG5cbiAgbGluay5zb3VyY2UgPSBmdW5jdGlvbihfKSB7XG4gICAgcmV0dXJuIGFyZ3VtZW50cy5sZW5ndGggPyAoc291cmNlID0gXywgbGluaykgOiBzb3VyY2U7XG4gIH07XG5cbiAgbGluay50YXJnZXQgPSBmdW5jdGlvbihfKSB7XG4gICAgcmV0dXJuIGFyZ3VtZW50cy5sZW5ndGggPyAodGFyZ2V0ID0gXywgbGluaykgOiB0YXJnZXQ7XG4gIH07XG5cbiAgbGluay54ID0gZnVuY3Rpb24oXykge1xuICAgIHJldHVybiBhcmd1bWVudHMubGVuZ3RoID8gKHggPSB0eXBlb2YgXyA9PT0gXCJmdW5jdGlvblwiID8gXyA6IGNvbnN0YW50KCtfKSwgbGluaykgOiB4O1xuICB9O1xuXG4gIGxpbmsueSA9IGZ1bmN0aW9uKF8pIHtcbiAgICByZXR1cm4gYXJndW1lbnRzLmxlbmd0aCA/ICh5ID0gdHlwZW9mIF8gPT09IFwiZnVuY3Rpb25cIiA/IF8gOiBjb25zdGFudCgrXyksIGxpbmspIDogeTtcbiAgfTtcblxuICBsaW5rLmNvbnRleHQgPSBmdW5jdGlvbihfKSB7XG4gICAgcmV0dXJuIGFyZ3VtZW50cy5sZW5ndGggPyAoKGNvbnRleHQgPSBfID09IG51bGwgPyBudWxsIDogXyksIGxpbmspIDogY29udGV4dDtcbiAgfTtcblxuICByZXR1cm4gbGluaztcbn1cblxuZnVuY3Rpb24gY3VydmVIb3Jpem9udGFsKGNvbnRleHQsIHgwLCB5MCwgeDEsIHkxKSB7XG4gIGNvbnRleHQubW92ZVRvKHgwLCB5MCk7XG4gIGNvbnRleHQuYmV6aWVyQ3VydmVUbyh4MCA9ICh4MCArIHgxKSAvIDIsIHkwLCB4MCwgeTEsIHgxLCB5MSk7XG59XG5cbmZ1bmN0aW9uIGN1cnZlVmVydGljYWwoY29udGV4dCwgeDAsIHkwLCB4MSwgeTEpIHtcbiAgY29udGV4dC5tb3ZlVG8oeDAsIHkwKTtcbiAgY29udGV4dC5iZXppZXJDdXJ2ZVRvKHgwLCB5MCA9ICh5MCArIHkxKSAvIDIsIHgxLCB5MCwgeDEsIHkxKTtcbn1cblxuZnVuY3Rpb24gY3VydmVSYWRpYWwoY29udGV4dCwgeDAsIHkwLCB4MSwgeTEpIHtcbiAgdmFyIHAwID0gcG9pbnRSYWRpYWwoeDAsIHkwKSxcbiAgICAgIHAxID0gcG9pbnRSYWRpYWwoeDAsIHkwID0gKHkwICsgeTEpIC8gMiksXG4gICAgICBwMiA9IHBvaW50UmFkaWFsKHgxLCB5MCksXG4gICAgICBwMyA9IHBvaW50UmFkaWFsKHgxLCB5MSk7XG4gIGNvbnRleHQubW92ZVRvKHAwWzBdLCBwMFsxXSk7XG4gIGNvbnRleHQuYmV6aWVyQ3VydmVUbyhwMVswXSwgcDFbMV0sIHAyWzBdLCBwMlsxXSwgcDNbMF0sIHAzWzFdKTtcbn1cblxuZXhwb3J0IGZ1bmN0aW9uIGxpbmtIb3Jpem9udGFsKCkge1xuICByZXR1cm4gbGluayhjdXJ2ZUhvcml6b250YWwpO1xufVxuXG5leHBvcnQgZnVuY3Rpb24gbGlua1ZlcnRpY2FsKCkge1xuICByZXR1cm4gbGluayhjdXJ2ZVZlcnRpY2FsKTtcbn1cblxuZXhwb3J0IGZ1bmN0aW9uIGxpbmtSYWRpYWwoKSB7XG4gIHZhciBsID0gbGluayhjdXJ2ZVJhZGlhbCk7XG4gIGwuYW5nbGUgPSBsLngsIGRlbGV0ZSBsLng7XG4gIGwucmFkaXVzID0gbC55LCBkZWxldGUgbC55O1xuICByZXR1cm4gbDtcbn1cbiIsImltcG9ydCBSZWFjdCBmcm9tICdyZWFjdCc7XG5pbXBvcnQgeyBsaW5rSG9yaXpvbnRhbCwgbGlua1ZlcnRpY2FsIH0gZnJvbSAnZDMtc2hhcGUnO1xuaW1wb3J0IHsgc2VsZWN0IH0gZnJvbSAnZDMtc2VsZWN0aW9uJztcbmV4cG9ydCBkZWZhdWx0IGNsYXNzIExpbmsgZXh0ZW5kcyBSZWFjdC5QdXJlQ29tcG9uZW50IHtcbiAgICBjb25zdHJ1Y3RvcigpIHtcbiAgICAgICAgc3VwZXIoLi4uYXJndW1lbnRzKTtcbiAgICAgICAgdGhpcy5saW5rUmVmID0gbnVsbDtcbiAgICAgICAgdGhpcy5zdGF0ZSA9IHtcbiAgICAgICAgICAgIGluaXRpYWxTdHlsZToge1xuICAgICAgICAgICAgICAgIG9wYWNpdHk6IDAsXG4gICAgICAgICAgICB9LFxuICAgICAgICB9O1xuICAgICAgICB0aGlzLmhhbmRsZU9uQ2xpY2sgPSBldnQgPT4ge1xuICAgICAgICAgICAgdGhpcy5wcm9wcy5vbkNsaWNrKHRoaXMucHJvcHMubGlua0RhdGEuc291cmNlLCB0aGlzLnByb3BzLmxpbmtEYXRhLnRhcmdldCwgZXZ0KTtcbiAgICAgICAgfTtcbiAgICAgICAgdGhpcy5oYW5kbGVPbk1vdXNlT3ZlciA9IGV2dCA9PiB7XG4gICAgICAgICAgICB0aGlzLnByb3BzLm9uTW91c2VPdmVyKHRoaXMucHJvcHMubGlua0RhdGEuc291cmNlLCB0aGlzLnByb3BzLmxpbmtEYXRhLnRhcmdldCwgZXZ0KTtcbiAgICAgICAgfTtcbiAgICAgICAgdGhpcy5oYW5kbGVPbk1vdXNlT3V0ID0gZXZ0ID0+IHtcbiAgICAgICAgICAgIHRoaXMucHJvcHMub25Nb3VzZU91dCh0aGlzLnByb3BzLmxpbmtEYXRhLnNvdXJjZSwgdGhpcy5wcm9wcy5saW5rRGF0YS50YXJnZXQsIGV2dCk7XG4gICAgICAgIH07XG4gICAgfVxuICAgIGNvbXBvbmVudERpZE1vdW50KCkge1xuICAgICAgICB0aGlzLmFwcGx5T3BhY2l0eSgxLCB0aGlzLnByb3BzLnRyYW5zaXRpb25EdXJhdGlvbik7XG4gICAgfVxuICAgIGNvbXBvbmVudFdpbGxMZWF2ZShkb25lKSB7XG4gICAgICAgIHRoaXMuYXBwbHlPcGFjaXR5KDAsIHRoaXMucHJvcHMudHJhbnNpdGlvbkR1cmF0aW9uLCBkb25lKTtcbiAgICB9XG4gICAgYXBwbHlPcGFjaXR5KG9wYWNpdHksIHRyYW5zaXRpb25EdXJhdGlvbiwgZG9uZSA9ICgpID0+IHsgfSkge1xuICAgICAgICBpZiAodGhpcy5wcm9wcy5lbmFibGVMZWdhY3lUcmFuc2l0aW9ucykge1xuICAgICAgICAgICAgc2VsZWN0KHRoaXMubGlua1JlZilcbiAgICAgICAgICAgICAgICAvLyBAdHMtaWdub3JlXG4gICAgICAgICAgICAgICAgLnRyYW5zaXRpb24oKVxuICAgICAgICAgICAgICAgIC5kdXJhdGlvbih0cmFuc2l0aW9uRHVyYXRpb24pXG4gICAgICAgICAgICAgICAgLnN0eWxlKCdvcGFjaXR5Jywgb3BhY2l0eSlcbiAgICAgICAgICAgICAgICAub24oJ2VuZCcsIGRvbmUpO1xuICAgICAgICB9XG4gICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgc2VsZWN0KHRoaXMubGlua1JlZikuc3R5bGUoJ29wYWNpdHknLCBvcGFjaXR5KTtcbiAgICAgICAgICAgIGRvbmUoKTtcbiAgICAgICAgfVxuICAgIH1cbiAgICBkcmF3U3RlcFBhdGgobGlua0RhdGEsIG9yaWVudGF0aW9uKSB7XG4gICAgICAgIGNvbnN0IHsgc291cmNlLCB0YXJnZXQgfSA9IGxpbmtEYXRhO1xuICAgICAgICBjb25zdCBkZWx0YVkgPSB0YXJnZXQueSAtIHNvdXJjZS55O1xuICAgICAgICByZXR1cm4gb3JpZW50YXRpb24gPT09ICdob3Jpem9udGFsJ1xuICAgICAgICAgICAgPyBgTSR7c291cmNlLnl9LCR7c291cmNlLnh9IEgke3NvdXJjZS55ICsgZGVsdGFZIC8gMn0gViR7dGFyZ2V0Lnh9IEgke3RhcmdldC55fWBcbiAgICAgICAgICAgIDogYE0ke3NvdXJjZS54fSwke3NvdXJjZS55fSBWJHtzb3VyY2UueSArIGRlbHRhWSAvIDJ9IEgke3RhcmdldC54fSBWJHt0YXJnZXQueX1gO1xuICAgIH1cbiAgICBkcmF3RGlhZ29uYWxQYXRoKGxpbmtEYXRhLCBvcmllbnRhdGlvbikge1xuICAgICAgICBjb25zdCB7IHNvdXJjZSwgdGFyZ2V0IH0gPSBsaW5rRGF0YTtcbiAgICAgICAgcmV0dXJuIG9yaWVudGF0aW9uID09PSAnaG9yaXpvbnRhbCdcbiAgICAgICAgICAgID8gbGlua0hvcml6b250YWwoKSh7XG4gICAgICAgICAgICAgICAgc291cmNlOiBbc291cmNlLnksIHNvdXJjZS54XSxcbiAgICAgICAgICAgICAgICB0YXJnZXQ6IFt0YXJnZXQueSwgdGFyZ2V0LnhdLFxuICAgICAgICAgICAgfSlcbiAgICAgICAgICAgIDogbGlua1ZlcnRpY2FsKCkoe1xuICAgICAgICAgICAgICAgIHNvdXJjZTogW3NvdXJjZS54LCBzb3VyY2UueV0sXG4gICAgICAgICAgICAgICAgdGFyZ2V0OiBbdGFyZ2V0LngsIHRhcmdldC55XSxcbiAgICAgICAgICAgIH0pO1xuICAgIH1cbiAgICBkcmF3U3RyYWlnaHRQYXRoKGxpbmtEYXRhLCBvcmllbnRhdGlvbikge1xuICAgICAgICBjb25zdCB7IHNvdXJjZSwgdGFyZ2V0IH0gPSBsaW5rRGF0YTtcbiAgICAgICAgcmV0dXJuIG9yaWVudGF0aW9uID09PSAnaG9yaXpvbnRhbCdcbiAgICAgICAgICAgID8gYE0ke3NvdXJjZS55fSwke3NvdXJjZS54fUwke3RhcmdldC55fSwke3RhcmdldC54fWBcbiAgICAgICAgICAgIDogYE0ke3NvdXJjZS54fSwke3NvdXJjZS55fUwke3RhcmdldC54fSwke3RhcmdldC55fWA7XG4gICAgfVxuICAgIGRyYXdFbGJvd1BhdGgobGlua0RhdGEsIG9yaWVudGF0aW9uKSB7XG4gICAgICAgIHJldHVybiBvcmllbnRhdGlvbiA9PT0gJ2hvcml6b250YWwnXG4gICAgICAgICAgICA/IGBNJHtsaW5rRGF0YS5zb3VyY2UueX0sJHtsaW5rRGF0YS5zb3VyY2UueH1WJHtsaW5rRGF0YS50YXJnZXQueH1IJHtsaW5rRGF0YS50YXJnZXQueX1gXG4gICAgICAgICAgICA6IGBNJHtsaW5rRGF0YS5zb3VyY2UueH0sJHtsaW5rRGF0YS5zb3VyY2UueX1WJHtsaW5rRGF0YS50YXJnZXQueX1IJHtsaW5rRGF0YS50YXJnZXQueH1gO1xuICAgIH1cbiAgICBkcmF3UGF0aCgpIHtcbiAgICAgICAgY29uc3QgeyBsaW5rRGF0YSwgb3JpZW50YXRpb24sIHBhdGhGdW5jIH0gPSB0aGlzLnByb3BzO1xuICAgICAgICBpZiAodHlwZW9mIHBhdGhGdW5jID09PSAnZnVuY3Rpb24nKSB7XG4gICAgICAgICAgICByZXR1cm4gcGF0aEZ1bmMobGlua0RhdGEsIG9yaWVudGF0aW9uKTtcbiAgICAgICAgfVxuICAgICAgICBpZiAocGF0aEZ1bmMgPT09ICdlbGJvdycpIHtcbiAgICAgICAgICAgIHJldHVybiB0aGlzLmRyYXdFbGJvd1BhdGgobGlua0RhdGEsIG9yaWVudGF0aW9uKTtcbiAgICAgICAgfVxuICAgICAgICBpZiAocGF0aEZ1bmMgPT09ICdzdHJhaWdodCcpIHtcbiAgICAgICAgICAgIHJldHVybiB0aGlzLmRyYXdTdHJhaWdodFBhdGgobGlua0RhdGEsIG9yaWVudGF0aW9uKTtcbiAgICAgICAgfVxuICAgICAgICBpZiAocGF0aEZ1bmMgPT09ICdzdGVwJykge1xuICAgICAgICAgICAgcmV0dXJuIHRoaXMuZHJhd1N0ZXBQYXRoKGxpbmtEYXRhLCBvcmllbnRhdGlvbik7XG4gICAgICAgIH1cbiAgICAgICAgcmV0dXJuIHRoaXMuZHJhd0RpYWdvbmFsUGF0aChsaW5rRGF0YSwgb3JpZW50YXRpb24pO1xuICAgIH1cbiAgICBnZXRDbGFzc05hbWVzKCkge1xuICAgICAgICBjb25zdCB7IGxpbmtEYXRhLCBvcmllbnRhdGlvbiwgcGF0aENsYXNzRnVuYyB9ID0gdGhpcy5wcm9wcztcbiAgICAgICAgY29uc3QgY2xhc3NOYW1lcyA9IFsncmQzdC1saW5rJ107XG4gICAgICAgIGlmICh0eXBlb2YgcGF0aENsYXNzRnVuYyA9PT0gJ2Z1bmN0aW9uJykge1xuICAgICAgICAgICAgY2xhc3NOYW1lcy5wdXNoKHBhdGhDbGFzc0Z1bmMobGlua0RhdGEsIG9yaWVudGF0aW9uKSk7XG4gICAgICAgIH1cbiAgICAgICAgcmV0dXJuIGNsYXNzTmFtZXMuam9pbignICcpLnRyaW0oKTtcbiAgICB9XG4gICAgcmVuZGVyKCkge1xuICAgICAgICBjb25zdCB7IGxpbmtEYXRhIH0gPSB0aGlzLnByb3BzO1xuICAgICAgICByZXR1cm4gKFJlYWN0LmNyZWF0ZUVsZW1lbnQoXCJwYXRoXCIsIHsgcmVmOiBsID0+IHtcbiAgICAgICAgICAgICAgICB0aGlzLmxpbmtSZWYgPSBsO1xuICAgICAgICAgICAgfSwgc3R5bGU6IE9iamVjdC5hc3NpZ24oe30sIHRoaXMuc3RhdGUuaW5pdGlhbFN0eWxlKSwgY2xhc3NOYW1lOiB0aGlzLmdldENsYXNzTmFtZXMoKSwgZDogdGhpcy5kcmF3UGF0aCgpLCBvbkNsaWNrOiB0aGlzLmhhbmRsZU9uQ2xpY2ssIG9uTW91c2VPdmVyOiB0aGlzLmhhbmRsZU9uTW91c2VPdmVyLCBvbk1vdXNlT3V0OiB0aGlzLmhhbmRsZU9uTW91c2VPdXQsIFwiZGF0YS1zb3VyY2UtaWRcIjogbGlua0RhdGEuc291cmNlLmlkLCBcImRhdGEtdGFyZ2V0LWlkXCI6IGxpbmtEYXRhLnRhcmdldC5pZCB9KSk7XG4gICAgfVxufVxuIiwiLy8gSW1wb3J0aW5nIENTUyBmaWxlcyBnbG9iYWxseSAoZS5nLiBgaW1wb3J0IFwiLi9zdHlsZXMuY3NzXCJgKSBjYW4gY2F1c2UgcmVzb2x1dGlvbiBpc3N1ZXMgd2l0aCBjZXJ0YWluXG4vLyBsaWJyYXJpZXMvZnJhbWV3b3Jrcy5cbi8vIEV4YW1wbGU6IE5leHQuanMgKGh0dHBzOi8vZ2l0aHViLmNvbS92ZXJjZWwvbmV4dC5qcy9ibG9iL21hc3Rlci9lcnJvcnMvY3NzLW5wbS5tZClcbi8vXG4vLyBTaW5jZSByZDN0J3MgQ1NTIGlzIGJhcmUgYm9uZXMgdG8gYmVnaW4gd2l0aCwgd2UgcHJvdmlkZSBhbGwgcmVxdWlyZWQgc3R5bGVzIGFzIGEgdGVtcGxhdGUgc3RyaW5nLFxuLy8gd2hpY2ggY2FuIGJlIGltcG9ydGVkIGxpa2UgYW55IG90aGVyIFRTL0pTIG1vZHVsZSBhbmQgaW5saW5lZCBpbnRvIGEgYDxzdHlsZT48L3N0eWxlPmAgdGFnLlxuZXhwb3J0IGRlZmF1bHQgYFxuLyogVHJlZSAqL1xuLnJkM3QtdHJlZS1jb250YWluZXIge1xuICB3aWR0aDogMTAwJTtcbiAgaGVpZ2h0OiAxMDAlO1xufVxuXG4ucmQzdC1ncmFiYmFibGUge1xuICBjdXJzb3I6IG1vdmU7IC8qIGZhbGxiYWNrIGlmIGdyYWIgY3Vyc29yIGlzIHVuc3VwcG9ydGVkICovXG4gIGN1cnNvcjogZ3JhYjtcbiAgY3Vyc29yOiAtbW96LWdyYWI7XG4gIGN1cnNvcjogLXdlYmtpdC1ncmFiO1xufVxuLnJkM3QtZ3JhYmJhYmxlOmFjdGl2ZSB7XG4gICAgY3Vyc29yOiBncmFiYmluZztcbiAgICBjdXJzb3I6IC1tb3otZ3JhYmJpbmc7XG4gICAgY3Vyc29yOiAtd2Via2l0LWdyYWJiaW5nO1xufVxuXG4vKiBOb2RlICovXG4ucmQzdC1ub2RlIHtcbiAgY3Vyc29yOiBwb2ludGVyO1xuICBmaWxsOiAjNzc3O1xuICBzdHJva2U6ICMwMDA7XG4gIHN0cm9rZS13aWR0aDogMjtcbn1cblxuLnJkM3QtbGVhZi1ub2RlIHtcbiAgY3Vyc29yOiBwb2ludGVyO1xuICBmaWxsOiB0cmFuc3BhcmVudDtcbiAgc3Ryb2tlOiAjMDAwO1xuICBzdHJva2Utd2lkdGg6IDE7XG59XG5cbi5yZDN0LWxhYmVsX190aXRsZSB7XG4gIGZpbGw6ICMwMDA7XG4gIHN0cm9rZTogbm9uZTtcbiAgZm9udC13ZWlnaHQ6IGJvbGRlcjtcbn1cblxuLnJkM3QtbGFiZWxfX2F0dHJpYnV0ZXMge1xuICBmaWxsOiAjNzc3O1xuICBzdHJva2U6IG5vbmU7XG4gIGZvbnQtd2VpZ2h0OiBib2xkZXI7XG4gIGZvbnQtc2l6ZTogc21hbGxlcjtcbn1cblxuLyogTGluayAqL1xuLnJkM3QtbGluayB7XG4gIGZpbGw6IG5vbmU7XG4gIHN0cm9rZTogIzAwMDtcbn1cbmA7XG4iLCJpbXBvcnQgUmVhY3QgZnJvbSAncmVhY3QnO1xuaW1wb3J0IHsgdHJlZSBhcyBkM3RyZWUsIGhpZXJhcmNoeSB9IGZyb20gJ2QzLWhpZXJhcmNoeSc7XG5pbXBvcnQgeyBzZWxlY3QgfSBmcm9tICdkMy1zZWxlY3Rpb24nO1xuaW1wb3J0IHsgem9vbSBhcyBkM3pvb20sIHpvb21JZGVudGl0eSB9IGZyb20gJ2QzLXpvb20nO1xuaW1wb3J0IHsgZGVxdWFsIGFzIGRlZXBFcXVhbCB9IGZyb20gJ2RlcXVhbC9saXRlJztcbmltcG9ydCBjbG9uZSBmcm9tICdjbG9uZSc7XG5pbXBvcnQgeyB2NCBhcyB1dWlkdjQgfSBmcm9tICd1dWlkJztcbmltcG9ydCBUcmFuc2l0aW9uR3JvdXBXcmFwcGVyIGZyb20gJy4vVHJhbnNpdGlvbkdyb3VwV3JhcHBlci5qcyc7XG5pbXBvcnQgTm9kZSBmcm9tICcuLi9Ob2RlL2luZGV4LmpzJztcbmltcG9ydCBMaW5rIGZyb20gJy4uL0xpbmsvaW5kZXguanMnO1xuaW1wb3J0IGdsb2JhbENzcyBmcm9tICcuLi9nbG9iYWxDc3MuanMnO1xuY2xhc3MgVHJlZSBleHRlbmRzIFJlYWN0LkNvbXBvbmVudCB7XG4gICAgY29uc3RydWN0b3IoKSB7XG4gICAgICAgIHN1cGVyKC4uLmFyZ3VtZW50cyk7XG4gICAgICAgIHRoaXMuc3RhdGUgPSB7XG4gICAgICAgICAgICBkYXRhUmVmOiB0aGlzLnByb3BzLmRhdGEsXG4gICAgICAgICAgICBkYXRhOiBUcmVlLmFzc2lnbkludGVybmFsUHJvcGVydGllcyhjbG9uZSh0aGlzLnByb3BzLmRhdGEpKSxcbiAgICAgICAgICAgIGQzOiBUcmVlLmNhbGN1bGF0ZUQzR2VvbWV0cnkodGhpcy5wcm9wcyksXG4gICAgICAgICAgICBpc1RyYW5zaXRpb25pbmc6IGZhbHNlLFxuICAgICAgICAgICAgaXNJbml0aWFsUmVuZGVyRm9yRGF0YXNldDogdHJ1ZSxcbiAgICAgICAgICAgIGRhdGFLZXk6IHRoaXMucHJvcHMuZGF0YUtleSxcbiAgICAgICAgfTtcbiAgICAgICAgdGhpcy5pbnRlcm5hbFN0YXRlID0ge1xuICAgICAgICAgICAgdGFyZ2V0Tm9kZTogbnVsbCxcbiAgICAgICAgICAgIGlzVHJhbnNpdGlvbmluZzogZmFsc2UsXG4gICAgICAgIH07XG4gICAgICAgIHRoaXMuc3ZnSW5zdGFuY2VSZWYgPSBgcmQzdC1zdmctJHt1dWlkdjQoKX1gO1xuICAgICAgICB0aGlzLmdJbnN0YW5jZVJlZiA9IGByZDN0LWctJHt1dWlkdjQoKX1gO1xuICAgICAgICAvKipcbiAgICAgICAgICogRmluZHMgdGhlIG5vZGUgbWF0Y2hpbmcgYG5vZGVJZGAgYW5kXG4gICAgICAgICAqIGV4cGFuZHMvY29sbGFwc2VzIGl0LCBkZXBlbmRpbmcgb24gdGhlIGN1cnJlbnQgc3RhdGUgb2ZcbiAgICAgICAgICogaXRzIGludGVybmFsIGBjb2xsYXBzZWRgIHByb3BlcnR5LlxuICAgICAgICAgKiBgc2V0U3RhdGVgIGNhbGxiYWNrIHJlY2VpdmVzIHRhcmdldE5vZGUgYW5kIGhhbmRsZXNcbiAgICAgICAgICogYHByb3BzLm9uQ2xpY2tgIGlmIGRlZmluZWQuXG4gICAgICAgICAqL1xuICAgICAgICB0aGlzLmhhbmRsZU5vZGVUb2dnbGUgPSAobm9kZUlkKSA9PiB7XG4gICAgICAgICAgICBjb25zdCBkYXRhID0gY2xvbmUodGhpcy5zdGF0ZS5kYXRhKTtcbiAgICAgICAgICAgIGNvbnN0IG1hdGNoZXMgPSB0aGlzLmZpbmROb2Rlc0J5SWQobm9kZUlkLCBkYXRhLCBbXSk7XG4gICAgICAgICAgICBjb25zdCB0YXJnZXROb2RlRGF0dW0gPSBtYXRjaGVzWzBdO1xuICAgICAgICAgICAgaWYgKHRoaXMucHJvcHMuY29sbGFwc2libGUgJiYgIXRoaXMuc3RhdGUuaXNUcmFuc2l0aW9uaW5nKSB7XG4gICAgICAgICAgICAgICAgaWYgKHRhcmdldE5vZGVEYXR1bS5fX3JkM3QuY29sbGFwc2VkKSB7XG4gICAgICAgICAgICAgICAgICAgIFRyZWUuZXhwYW5kTm9kZSh0YXJnZXROb2RlRGF0dW0pO1xuICAgICAgICAgICAgICAgICAgICB0aGlzLnByb3BzLnNob3VsZENvbGxhcHNlTmVpZ2hib3JOb2RlcyAmJiB0aGlzLmNvbGxhcHNlTmVpZ2hib3JOb2Rlcyh0YXJnZXROb2RlRGF0dW0sIGRhdGEpO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgVHJlZS5jb2xsYXBzZU5vZGUodGFyZ2V0Tm9kZURhdHVtKTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgaWYgKHRoaXMucHJvcHMuZW5hYmxlTGVnYWN5VHJhbnNpdGlvbnMpIHtcbiAgICAgICAgICAgICAgICAgICAgLy8gTG9jayBub2RlIHRvZ2dsaW5nIHdoaWxlIHRyYW5zaXRpb24gdGFrZXMgcGxhY2UuXG4gICAgICAgICAgICAgICAgICAgIHRoaXMuc2V0U3RhdGUoeyBkYXRhLCBpc1RyYW5zaXRpb25pbmc6IHRydWUgfSk7XG4gICAgICAgICAgICAgICAgICAgIC8vIEF3YWl0IHRyYW5zaXRpb25EdXJhdGlvbiArIDEwIG1zIGJlZm9yZSB1bmxvY2tpbmcgbm9kZSB0b2dnbGluZyBhZ2Fpbi5cbiAgICAgICAgICAgICAgICAgICAgc2V0VGltZW91dCgoKSA9PiB0aGlzLnNldFN0YXRlKHsgaXNUcmFuc2l0aW9uaW5nOiBmYWxzZSB9KSwgdGhpcy5wcm9wcy50cmFuc2l0aW9uRHVyYXRpb24gKyAxMCk7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIGVsc2Uge1xuICAgICAgICAgICAgICAgICAgICB0aGlzLnNldFN0YXRlKHsgZGF0YSB9KTtcbiAgICAgICAgICAgICAgICB9XG4gICAgICAgICAgICAgICAgdGhpcy5pbnRlcm5hbFN0YXRlLnRhcmdldE5vZGUgPSB0YXJnZXROb2RlRGF0dW07XG4gICAgICAgICAgICB9XG4gICAgICAgIH07XG4gICAgICAgIHRoaXMuaGFuZGxlQWRkQ2hpbGRyZW5Ub05vZGUgPSAobm9kZUlkLCBjaGlsZHJlbkRhdGEpID0+IHtcbiAgICAgICAgICAgIGNvbnN0IGRhdGEgPSBjbG9uZSh0aGlzLnN0YXRlLmRhdGEpO1xuICAgICAgICAgICAgY29uc3QgbWF0Y2hlcyA9IHRoaXMuZmluZE5vZGVzQnlJZChub2RlSWQsIGRhdGEsIFtdKTtcbiAgICAgICAgICAgIGlmIChtYXRjaGVzLmxlbmd0aCA+IDApIHtcbiAgICAgICAgICAgICAgICBjb25zdCB0YXJnZXROb2RlRGF0dW0gPSBtYXRjaGVzWzBdO1xuICAgICAgICAgICAgICAgIGNvbnN0IGRlcHRoID0gdGFyZ2V0Tm9kZURhdHVtLl9fcmQzdC5kZXB0aDtcbiAgICAgICAgICAgICAgICBjb25zdCBmb3JtYXR0ZWRDaGlsZHJlbiA9IGNsb25lKGNoaWxkcmVuRGF0YSkubWFwKChub2RlKSA9PiBUcmVlLmFzc2lnbkludGVybmFsUHJvcGVydGllcyhbbm9kZV0sIGRlcHRoICsgMSkpO1xuICAgICAgICAgICAgICAgIHRhcmdldE5vZGVEYXR1bS5jaGlsZHJlbi5wdXNoKC4uLmZvcm1hdHRlZENoaWxkcmVuLmZsYXQoKSk7XG4gICAgICAgICAgICAgICAgdGhpcy5zZXRTdGF0ZSh7IGRhdGEgfSk7XG4gICAgICAgICAgICB9XG4gICAgICAgIH07XG4gICAgICAgIC8qKlxuICAgICAgICAgKiBIYW5kbGVzIHRoZSB1c2VyLWRlZmluZWQgYG9uTm9kZUNsaWNrYCBmdW5jdGlvbi5cbiAgICAgICAgICovXG4gICAgICAgIHRoaXMuaGFuZGxlT25Ob2RlQ2xpY2tDYiA9IChoaWVyYXJjaHlQb2ludE5vZGUsIGV2dCkgPT4ge1xuICAgICAgICAgICAgY29uc3QgeyBvbk5vZGVDbGljayB9ID0gdGhpcy5wcm9wcztcbiAgICAgICAgICAgIGlmIChvbk5vZGVDbGljayAmJiB0eXBlb2Ygb25Ob2RlQ2xpY2sgPT09ICdmdW5jdGlvbicpIHtcbiAgICAgICAgICAgICAgICAvLyBQZXJzaXN0IHRoZSBTeW50aGV0aWNFdmVudCBmb3IgZG93bnN0cmVhbSBoYW5kbGluZyBieSB1c2Vycy5cbiAgICAgICAgICAgICAgICBldnQucGVyc2lzdCgpO1xuICAgICAgICAgICAgICAgIG9uTm9kZUNsaWNrKGNsb25lKGhpZXJhcmNoeVBvaW50Tm9kZSksIGV2dCk7XG4gICAgICAgICAgICB9XG4gICAgICAgIH07XG4gICAgICAgIC8qKlxuICAgICAgICAgKiBIYW5kbGVzIHRoZSB1c2VyLWRlZmluZWQgYG9uTGlua0NsaWNrYCBmdW5jdGlvbi5cbiAgICAgICAgICovXG4gICAgICAgIHRoaXMuaGFuZGxlT25MaW5rQ2xpY2tDYiA9IChsaW5rU291cmNlLCBsaW5rVGFyZ2V0LCBldnQpID0+IHtcbiAgICAgICAgICAgIGNvbnN0IHsgb25MaW5rQ2xpY2sgfSA9IHRoaXMucHJvcHM7XG4gICAgICAgICAgICBpZiAob25MaW5rQ2xpY2sgJiYgdHlwZW9mIG9uTGlua0NsaWNrID09PSAnZnVuY3Rpb24nKSB7XG4gICAgICAgICAgICAgICAgLy8gUGVyc2lzdCB0aGUgU3ludGhldGljRXZlbnQgZm9yIGRvd25zdHJlYW0gaGFuZGxpbmcgYnkgdXNlcnMuXG4gICAgICAgICAgICAgICAgZXZ0LnBlcnNpc3QoKTtcbiAgICAgICAgICAgICAgICBvbkxpbmtDbGljayhjbG9uZShsaW5rU291cmNlKSwgY2xvbmUobGlua1RhcmdldCksIGV2dCk7XG4gICAgICAgICAgICB9XG4gICAgICAgIH07XG4gICAgICAgIC8qKlxuICAgICAgICAgKiBIYW5kbGVzIHRoZSB1c2VyLWRlZmluZWQgYG9uTm9kZU1vdXNlT3ZlcmAgZnVuY3Rpb24uXG4gICAgICAgICAqL1xuICAgICAgICB0aGlzLmhhbmRsZU9uTm9kZU1vdXNlT3ZlckNiID0gKGhpZXJhcmNoeVBvaW50Tm9kZSwgZXZ0KSA9PiB7XG4gICAgICAgICAgICBjb25zdCB7IG9uTm9kZU1vdXNlT3ZlciB9ID0gdGhpcy5wcm9wcztcbiAgICAgICAgICAgIGlmIChvbk5vZGVNb3VzZU92ZXIgJiYgdHlwZW9mIG9uTm9kZU1vdXNlT3ZlciA9PT0gJ2Z1bmN0aW9uJykge1xuICAgICAgICAgICAgICAgIC8vIFBlcnNpc3QgdGhlIFN5bnRoZXRpY0V2ZW50IGZvciBkb3duc3RyZWFtIGhhbmRsaW5nIGJ5IHVzZXJzLlxuICAgICAgICAgICAgICAgIGV2dC5wZXJzaXN0KCk7XG4gICAgICAgICAgICAgICAgb25Ob2RlTW91c2VPdmVyKGNsb25lKGhpZXJhcmNoeVBvaW50Tm9kZSksIGV2dCk7XG4gICAgICAgICAgICB9XG4gICAgICAgIH07XG4gICAgICAgIC8qKlxuICAgICAgICAgKiBIYW5kbGVzIHRoZSB1c2VyLWRlZmluZWQgYG9uTGlua01vdXNlT3ZlcmAgZnVuY3Rpb24uXG4gICAgICAgICAqL1xuICAgICAgICB0aGlzLmhhbmRsZU9uTGlua01vdXNlT3ZlckNiID0gKGxpbmtTb3VyY2UsIGxpbmtUYXJnZXQsIGV2dCkgPT4ge1xuICAgICAgICAgICAgY29uc3QgeyBvbkxpbmtNb3VzZU92ZXIgfSA9IHRoaXMucHJvcHM7XG4gICAgICAgICAgICBpZiAob25MaW5rTW91c2VPdmVyICYmIHR5cGVvZiBvbkxpbmtNb3VzZU92ZXIgPT09ICdmdW5jdGlvbicpIHtcbiAgICAgICAgICAgICAgICAvLyBQZXJzaXN0IHRoZSBTeW50aGV0aWNFdmVudCBmb3IgZG93bnN0cmVhbSBoYW5kbGluZyBieSB1c2Vycy5cbiAgICAgICAgICAgICAgICBldnQucGVyc2lzdCgpO1xuICAgICAgICAgICAgICAgIG9uTGlua01vdXNlT3ZlcihjbG9uZShsaW5rU291cmNlKSwgY2xvbmUobGlua1RhcmdldCksIGV2dCk7XG4gICAgICAgICAgICB9XG4gICAgICAgIH07XG4gICAgICAgIC8qKlxuICAgICAgICAgKiBIYW5kbGVzIHRoZSB1c2VyLWRlZmluZWQgYG9uTm9kZU1vdXNlT3V0YCBmdW5jdGlvbi5cbiAgICAgICAgICovXG4gICAgICAgIHRoaXMuaGFuZGxlT25Ob2RlTW91c2VPdXRDYiA9IChoaWVyYXJjaHlQb2ludE5vZGUsIGV2dCkgPT4ge1xuICAgICAgICAgICAgY29uc3QgeyBvbk5vZGVNb3VzZU91dCB9ID0gdGhpcy5wcm9wcztcbiAgICAgICAgICAgIGlmIChvbk5vZGVNb3VzZU91dCAmJiB0eXBlb2Ygb25Ob2RlTW91c2VPdXQgPT09ICdmdW5jdGlvbicpIHtcbiAgICAgICAgICAgICAgICAvLyBQZXJzaXN0IHRoZSBTeW50aGV0aWNFdmVudCBmb3IgZG93bnN0cmVhbSBoYW5kbGluZyBieSB1c2Vycy5cbiAgICAgICAgICAgICAgICBldnQucGVyc2lzdCgpO1xuICAgICAgICAgICAgICAgIG9uTm9kZU1vdXNlT3V0KGNsb25lKGhpZXJhcmNoeVBvaW50Tm9kZSksIGV2dCk7XG4gICAgICAgICAgICB9XG4gICAgICAgIH07XG4gICAgICAgIC8qKlxuICAgICAgICAgKiBIYW5kbGVzIHRoZSB1c2VyLWRlZmluZWQgYG9uTGlua01vdXNlT3V0YCBmdW5jdGlvbi5cbiAgICAgICAgICovXG4gICAgICAgIHRoaXMuaGFuZGxlT25MaW5rTW91c2VPdXRDYiA9IChsaW5rU291cmNlLCBsaW5rVGFyZ2V0LCBldnQpID0+IHtcbiAgICAgICAgICAgIGNvbnN0IHsgb25MaW5rTW91c2VPdXQgfSA9IHRoaXMucHJvcHM7XG4gICAgICAgICAgICBpZiAob25MaW5rTW91c2VPdXQgJiYgdHlwZW9mIG9uTGlua01vdXNlT3V0ID09PSAnZnVuY3Rpb24nKSB7XG4gICAgICAgICAgICAgICAgLy8gUGVyc2lzdCB0aGUgU3ludGhldGljRXZlbnQgZm9yIGRvd25zdHJlYW0gaGFuZGxpbmcgYnkgdXNlcnMuXG4gICAgICAgICAgICAgICAgZXZ0LnBlcnNpc3QoKTtcbiAgICAgICAgICAgICAgICBvbkxpbmtNb3VzZU91dChjbG9uZShsaW5rU291cmNlKSwgY2xvbmUobGlua1RhcmdldCksIGV2dCk7XG4gICAgICAgICAgICB9XG4gICAgICAgIH07XG4gICAgICAgIC8qKlxuICAgICAgICAgKiBUYWtlcyBhIGhpZXJhcmNoeSBwb2ludCBub2RlIGFuZCBjZW50ZXJzIHRoZSBub2RlIG9uIHRoZSBzY3JlZW5cbiAgICAgICAgICogaWYgdGhlIGRpbWVuc2lvbnMgcGFyYW1ldGVyIGlzIHBhc3NlZCB0byBgVHJlZWAuXG4gICAgICAgICAqXG4gICAgICAgICAqIFRoaXMgY29kZSBpcyBhZGFwdGVkIGZyb20gUm9iIFNjaG11ZWNrZXIncyBjZW50ZXJOb2RlIG1ldGhvZC5cbiAgICAgICAgICogTGluazogaHR0cDovL2JsLm9ja3Mub3JnL3JvYnNjaG11ZWNrZXIvNzg4MDAzM1xuICAgICAgICAgKi9cbiAgICAgICAgdGhpcy5jZW50ZXJOb2RlID0gKGhpZXJhcmNoeVBvaW50Tm9kZSkgPT4ge1xuICAgICAgICAgICAgY29uc3QgeyBkaW1lbnNpb25zLCBvcmllbnRhdGlvbiwgem9vbSwgY2VudGVyaW5nVHJhbnNpdGlvbkR1cmF0aW9uIH0gPSB0aGlzLnByb3BzO1xuICAgICAgICAgICAgaWYgKGRpbWVuc2lvbnMpIHtcbiAgICAgICAgICAgICAgICBjb25zdCBnID0gc2VsZWN0KGAuJHt0aGlzLmdJbnN0YW5jZVJlZn1gKTtcbiAgICAgICAgICAgICAgICBjb25zdCBzdmcgPSBzZWxlY3QoYC4ke3RoaXMuc3ZnSW5zdGFuY2VSZWZ9YCk7XG4gICAgICAgICAgICAgICAgY29uc3Qgc2NhbGUgPSB0aGlzLnN0YXRlLmQzLnNjYWxlO1xuICAgICAgICAgICAgICAgIGxldCB4O1xuICAgICAgICAgICAgICAgIGxldCB5O1xuICAgICAgICAgICAgICAgIC8vIGlmIHRoZSBvcmllbnRhdGlvbiBpcyBob3Jpem9udGFsLCBjYWxjdWxhdGUgdGhlIHZhcmlhYmxlcyBpbnZlcnRlZCAoeC0+eSwgeS0+eClcbiAgICAgICAgICAgICAgICBpZiAob3JpZW50YXRpb24gPT09ICdob3Jpem9udGFsJykge1xuICAgICAgICAgICAgICAgICAgICB5ID0gLWhpZXJhcmNoeVBvaW50Tm9kZS54ICogc2NhbGUgKyBkaW1lbnNpb25zLmhlaWdodCAvIDI7XG4gICAgICAgICAgICAgICAgICAgIHggPSAtaGllcmFyY2h5UG9pbnROb2RlLnkgKiBzY2FsZSArIGRpbWVuc2lvbnMud2lkdGggLyAyO1xuICAgICAgICAgICAgICAgIH1cbiAgICAgICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICAgICAgLy8gZWxzZSwgY2FsY3VsYXRlIHRoZSB2YXJpYWJsZXMgbm9ybWFsbHkgKHgtPngsIHktPnkpXG4gICAgICAgICAgICAgICAgICAgIHggPSAtaGllcmFyY2h5UG9pbnROb2RlLnggKiBzY2FsZSArIGRpbWVuc2lvbnMud2lkdGggLyAyO1xuICAgICAgICAgICAgICAgICAgICB5ID0gLWhpZXJhcmNoeVBvaW50Tm9kZS55ICogc2NhbGUgKyBkaW1lbnNpb25zLmhlaWdodCAvIDI7XG4gICAgICAgICAgICAgICAgfVxuICAgICAgICAgICAgICAgIC8vQHRzLWlnbm9yZVxuICAgICAgICAgICAgICAgIGcudHJhbnNpdGlvbigpXG4gICAgICAgICAgICAgICAgICAgIC5kdXJhdGlvbihjZW50ZXJpbmdUcmFuc2l0aW9uRHVyYXRpb24pXG4gICAgICAgICAgICAgICAgICAgIC5hdHRyKCd0cmFuc2Zvcm0nLCAndHJhbnNsYXRlKCcgKyB4ICsgJywnICsgeSArICcpc2NhbGUoJyArIHNjYWxlICsgJyknKTtcbiAgICAgICAgICAgICAgICAvLyBTZXRzIHRoZSB2aWV3cG9ydCB0byB0aGUgbmV3IGNlbnRlciBzbyB0aGF0IGl0IGRvZXMgbm90IGp1bXAgYmFjayB0byBvcmlnaW5hbFxuICAgICAgICAgICAgICAgIC8vIGNvb3JkaW5hdGVzIHdoZW4gZHJhZ2dlZC96b29tZWRcbiAgICAgICAgICAgICAgICAvL0B0cy1pZ25vcmVcbiAgICAgICAgICAgICAgICBzdmcuY2FsbChkM3pvb20oKS50cmFuc2Zvcm0sIHpvb21JZGVudGl0eS50cmFuc2xhdGUoeCwgeSkuc2NhbGUoem9vbSkpO1xuICAgICAgICAgICAgfVxuICAgICAgICB9O1xuICAgICAgICAvKipcbiAgICAgICAgICogRGV0ZXJtaW5lcyB3aGljaCBhZGRpdGlvbmFsIGBjbGFzc05hbWVgIHByb3Agc2hvdWxkIGJlIHBhc3NlZCB0byB0aGUgbm9kZSAmIHJldHVybnMgaXQuXG4gICAgICAgICAqL1xuICAgICAgICB0aGlzLmdldE5vZGVDbGFzc05hbWUgPSAocGFyZW50LCBub2RlRGF0dW0pID0+IHtcbiAgICAgICAgICAgIGNvbnN0IHsgcm9vdE5vZGVDbGFzc05hbWUsIGJyYW5jaE5vZGVDbGFzc05hbWUsIGxlYWZOb2RlQ2xhc3NOYW1lIH0gPSB0aGlzLnByb3BzO1xuICAgICAgICAgICAgY29uc3QgaGFzUGFyZW50ID0gcGFyZW50ICE9PSBudWxsICYmIHBhcmVudCAhPT0gdW5kZWZpbmVkO1xuICAgICAgICAgICAgaWYgKGhhc1BhcmVudCkge1xuICAgICAgICAgICAgICAgIHJldHVybiBub2RlRGF0dW0uY2hpbGRyZW4gPyBicmFuY2hOb2RlQ2xhc3NOYW1lIDogbGVhZk5vZGVDbGFzc05hbWU7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICBlbHNlIHtcbiAgICAgICAgICAgICAgICByZXR1cm4gcm9vdE5vZGVDbGFzc05hbWU7XG4gICAgICAgICAgICB9XG4gICAgICAgIH07XG4gICAgfVxuICAgIHN0YXRpYyBnZXREZXJpdmVkU3RhdGVGcm9tUHJvcHMobmV4dFByb3BzLCBwcmV2U3RhdGUpIHtcbiAgICAgICAgbGV0IGRlcml2ZWRTdGF0ZSA9IG51bGw7XG4gICAgICAgIC8vIENsb25lIG5ldyBkYXRhICYgYXNzaWduIGludGVybmFsIHByb3BlcnRpZXMgaWYgYGRhdGFgIG9iamVjdCByZWZlcmVuY2UgY2hhbmdlZC5cbiAgICAgICAgLy8gSWYgdGhlIGRhdGFLZXkgd2FzIHByZXNlbnQgYnV0IGRpZG4ndCBjaGFuZ2UsIHRoZW4gd2UgZG9uJ3QgbmVlZCB0byByZS1yZW5kZXIgdGhlIHRyZWVcbiAgICAgICAgY29uc3QgZGF0YUtleUNoYW5nZWQgPSAhbmV4dFByb3BzLmRhdGFLZXkgfHwgcHJldlN0YXRlLmRhdGFLZXkgIT09IG5leHRQcm9wcy5kYXRhS2V5O1xuICAgICAgICBpZiAobmV4dFByb3BzLmRhdGEgIT09IHByZXZTdGF0ZS5kYXRhUmVmICYmIGRhdGFLZXlDaGFuZ2VkKSB7XG4gICAgICAgICAgICBkZXJpdmVkU3RhdGUgPSB7XG4gICAgICAgICAgICAgICAgZGF0YVJlZjogbmV4dFByb3BzLmRhdGEsXG4gICAgICAgICAgICAgICAgZGF0YTogVHJlZS5hc3NpZ25JbnRlcm5hbFByb3BlcnRpZXMoY2xvbmUobmV4dFByb3BzLmRhdGEpKSxcbiAgICAgICAgICAgICAgICBpc0luaXRpYWxSZW5kZXJGb3JEYXRhc2V0OiB0cnVlLFxuICAgICAgICAgICAgICAgIGRhdGFLZXk6IG5leHRQcm9wcy5kYXRhS2V5LFxuICAgICAgICAgICAgfTtcbiAgICAgICAgfVxuICAgICAgICBjb25zdCBkMyA9IFRyZWUuY2FsY3VsYXRlRDNHZW9tZXRyeShuZXh0UHJvcHMpO1xuICAgICAgICBpZiAoIWRlZXBFcXVhbChkMywgcHJldlN0YXRlLmQzKSkge1xuICAgICAgICAgICAgZGVyaXZlZFN0YXRlID0gZGVyaXZlZFN0YXRlIHx8IHt9O1xuICAgICAgICAgICAgZGVyaXZlZFN0YXRlLmQzID0gZDM7XG4gICAgICAgIH1cbiAgICAgICAgcmV0dXJuIGRlcml2ZWRTdGF0ZTtcbiAgICB9XG4gICAgY29tcG9uZW50RGlkTW91bnQoKSB7XG4gICAgICAgIHRoaXMuYmluZFpvb21MaXN0ZW5lcih0aGlzLnByb3BzKTtcbiAgICAgICAgdGhpcy5zZXRTdGF0ZSh7IGlzSW5pdGlhbFJlbmRlckZvckRhdGFzZXQ6IGZhbHNlIH0pO1xuICAgIH1cbiAgICBjb21wb25lbnREaWRVcGRhdGUocHJldlByb3BzKSB7XG4gICAgICAgIGlmICh0aGlzLnByb3BzLmRhdGEgIT09IHByZXZQcm9wcy5kYXRhKSB7XG4gICAgICAgICAgICAvLyBJZiBsYXN0IGByZW5kZXJgIHdhcyBkdWUgdG8gY2hhbmdlIGluIGRhdGFzZXQgLT4gbWFyayB0aGUgaW5pdGlhbCByZW5kZXIgYXMgZG9uZS5cbiAgICAgICAgICAgIHRoaXMuc2V0U3RhdGUoeyBpc0luaXRpYWxSZW5kZXJGb3JEYXRhc2V0OiBmYWxzZSB9KTtcbiAgICAgICAgfVxuICAgICAgICBpZiAoIWRlZXBFcXVhbCh0aGlzLnByb3BzLnRyYW5zbGF0ZSwgcHJldlByb3BzLnRyYW5zbGF0ZSkgfHxcbiAgICAgICAgICAgICFkZWVwRXF1YWwodGhpcy5wcm9wcy5zY2FsZUV4dGVudCwgcHJldlByb3BzLnNjYWxlRXh0ZW50KSB8fFxuICAgICAgICAgICAgdGhpcy5wcm9wcy56b29tYWJsZSAhPT0gcHJldlByb3BzLnpvb21hYmxlIHx8XG4gICAgICAgICAgICB0aGlzLnByb3BzLmRyYWdnYWJsZSAhPT0gcHJldlByb3BzLmRyYWdnYWJsZSB8fFxuICAgICAgICAgICAgdGhpcy5wcm9wcy56b29tICE9PSBwcmV2UHJvcHMuem9vbSB8fFxuICAgICAgICAgICAgdGhpcy5wcm9wcy5lbmFibGVMZWdhY3lUcmFuc2l0aW9ucyAhPT0gcHJldlByb3BzLmVuYWJsZUxlZ2FjeVRyYW5zaXRpb25zKSB7XG4gICAgICAgICAgICAvLyBJZiB6b29tLXNwZWNpZmljIHByb3BzIGNoYW5nZSAtPiByZWJpbmQgbGlzdGVuZXIgd2l0aCBuZXcgdmFsdWVzLlxuICAgICAgICAgICAgLy8gT3I6IHJlYmluZCB6b29tIGxpc3RlbmVycyB0byBuZXcgRE9NIG5vZGVzIGluIGNhc2UgbGVnYWN5IHRyYW5zaXRpb25zIHdlcmUgZW5hYmxlZC9kaXNhYmxlZC5cbiAgICAgICAgICAgIHRoaXMuYmluZFpvb21MaXN0ZW5lcih0aGlzLnByb3BzKTtcbiAgICAgICAgfVxuICAgICAgICBpZiAodHlwZW9mIHRoaXMucHJvcHMub25VcGRhdGUgPT09ICdmdW5jdGlvbicpIHtcbiAgICAgICAgICAgIHRoaXMucHJvcHMub25VcGRhdGUoe1xuICAgICAgICAgICAgICAgIG5vZGU6IHRoaXMuaW50ZXJuYWxTdGF0ZS50YXJnZXROb2RlID8gY2xvbmUodGhpcy5pbnRlcm5hbFN0YXRlLnRhcmdldE5vZGUpIDogbnVsbCxcbiAgICAgICAgICAgICAgICB6b29tOiB0aGlzLnN0YXRlLmQzLnNjYWxlLFxuICAgICAgICAgICAgICAgIHRyYW5zbGF0ZTogdGhpcy5zdGF0ZS5kMy50cmFuc2xhdGUsXG4gICAgICAgICAgICB9KTtcbiAgICAgICAgfVxuICAgICAgICAvLyBSZXNldCB0aGUgbGFzdCB0YXJnZXQgbm9kZSBhZnRlciB3ZSd2ZSBmbHVzaGVkIGl0IHRvIGBvblVwZGF0ZWAuXG4gICAgICAgIHRoaXMuaW50ZXJuYWxTdGF0ZS50YXJnZXROb2RlID0gbnVsbDtcbiAgICB9XG4gICAgLyoqXG4gICAgICogQ29sbGFwc2VzIGFsbCB0cmVlIG5vZGVzIHdpdGggYSBgZGVwdGhgIGxhcmdlciB0aGFuIGBpbml0aWFsRGVwdGhgLlxuICAgICAqXG4gICAgICogQHBhcmFtIHthcnJheX0gbm9kZVNldCBBcnJheSBvZiBub2RlcyBnZW5lcmF0ZWQgYnkgYGdlbmVyYXRlVHJlZWBcbiAgICAgKiBAcGFyYW0ge251bWJlcn0gaW5pdGlhbERlcHRoIE1heGltdW0gaW5pdGlhbCBkZXB0aCB0aGUgdHJlZSBzaG91bGQgcmVuZGVyXG4gICAgICovXG4gICAgc2V0SW5pdGlhbFRyZWVEZXB0aChub2RlU2V0LCBpbml0aWFsRGVwdGgpIHtcbiAgICAgICAgbm9kZVNldC5mb3JFYWNoKG4gPT4ge1xuICAgICAgICAgICAgbi5kYXRhLl9fcmQzdC5jb2xsYXBzZWQgPSBuLmRlcHRoID49IGluaXRpYWxEZXB0aDtcbiAgICAgICAgfSk7XG4gICAgfVxuICAgIC8qKlxuICAgICAqIGJpbmRab29tTGlzdGVuZXIgLSBJZiBgcHJvcHMuem9vbWFibGVgLCBiaW5kcyBhIGxpc3RlbmVyIGZvclxuICAgICAqIFwiem9vbVwiIGV2ZW50cyB0byB0aGUgU1ZHIGFuZCBzZXRzIHNjYWxlRXh0ZW50IHRvIG1pbi9tYXhcbiAgICAgKiBzcGVjaWZpZWQgaW4gYHByb3BzLnNjYWxlRXh0ZW50YC5cbiAgICAgKi9cbiAgICBiaW5kWm9vbUxpc3RlbmVyKHByb3BzKSB7XG4gICAgICAgIGNvbnN0IHsgem9vbWFibGUsIHNjYWxlRXh0ZW50LCB0cmFuc2xhdGUsIHpvb20sIG9uVXBkYXRlLCBoYXNJbnRlcmFjdGl2ZU5vZGVzIH0gPSBwcm9wcztcbiAgICAgICAgY29uc3Qgc3ZnID0gc2VsZWN0KGAuJHt0aGlzLnN2Z0luc3RhbmNlUmVmfWApO1xuICAgICAgICBjb25zdCBnID0gc2VsZWN0KGAuJHt0aGlzLmdJbnN0YW5jZVJlZn1gKTtcbiAgICAgICAgLy8gU2V0cyBpbml0aWFsIG9mZnNldCwgc28gdGhhdCBmaXJzdCBwYW4gYW5kIHpvb20gZG9lcyBub3QganVtcCBiYWNrIHRvIGRlZmF1bHQgWzAsMF0gY29vcmRzLlxuICAgICAgICAvLyBAdHMtaWdub3JlXG4gICAgICAgIHN2Zy5jYWxsKGQzem9vbSgpLnRyYW5zZm9ybSwgem9vbUlkZW50aXR5LnRyYW5zbGF0ZSh0cmFuc2xhdGUueCwgdHJhbnNsYXRlLnkpLnNjYWxlKHpvb20pKTtcbiAgICAgICAgc3ZnLmNhbGwoZDN6b29tKClcbiAgICAgICAgICAgIC5zY2FsZUV4dGVudCh6b29tYWJsZSA/IFtzY2FsZUV4dGVudC5taW4sIHNjYWxlRXh0ZW50Lm1heF0gOiBbem9vbSwgem9vbV0pXG4gICAgICAgICAgICAvLyBUT0RPOiBicmVhayB0aGlzIG91dCBpbnRvIGEgc2VwYXJhdGUgem9vbSBoYW5kbGVyIGZuLCByYXRoZXIgdGhhbiBpbmxpbmluZyBpdC5cbiAgICAgICAgICAgIC5maWx0ZXIoKGV2ZW50KSA9PiB7XG4gICAgICAgICAgICBpZiAoaGFzSW50ZXJhY3RpdmVOb2Rlcykge1xuICAgICAgICAgICAgICAgIHJldHVybiAoZXZlbnQudGFyZ2V0LmNsYXNzTGlzdC5jb250YWlucyh0aGlzLnN2Z0luc3RhbmNlUmVmKSB8fFxuICAgICAgICAgICAgICAgICAgICBldmVudC50YXJnZXQuY2xhc3NMaXN0LmNvbnRhaW5zKHRoaXMuZ0luc3RhbmNlUmVmKSB8fFxuICAgICAgICAgICAgICAgICAgICBldmVudC5zaGlmdEtleSk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICByZXR1cm4gdHJ1ZTtcbiAgICAgICAgfSlcbiAgICAgICAgICAgIC5vbignem9vbScsIChldmVudCkgPT4ge1xuICAgICAgICAgICAgaWYgKCF0aGlzLnByb3BzLmRyYWdnYWJsZSAmJlxuICAgICAgICAgICAgICAgIFsnbW91c2Vtb3ZlJywgJ3RvdWNobW92ZScsICdkYmxjbGljayddLmluY2x1ZGVzKGV2ZW50LnNvdXJjZUV2ZW50LnR5cGUpKSB7XG4gICAgICAgICAgICAgICAgcmV0dXJuO1xuICAgICAgICAgICAgfVxuICAgICAgICAgICAgZy5hdHRyKCd0cmFuc2Zvcm0nLCBldmVudC50cmFuc2Zvcm0pO1xuICAgICAgICAgICAgaWYgKHR5cGVvZiBvblVwZGF0ZSA9PT0gJ2Z1bmN0aW9uJykge1xuICAgICAgICAgICAgICAgIC8vIFRoaXMgY2FsbGJhY2sgaXMgbWFnaWNhbGx5IGNhbGxlZCBub3Qgb25seSBvbiBcInpvb21cIiwgYnV0IG9uIFwiZHJhZ1wiLCBhcyB3ZWxsLFxuICAgICAgICAgICAgICAgIC8vIGV2ZW4gdGhvdWdoIGV2ZW50LnR5cGUgPT0gXCJ6b29tXCIuXG4gICAgICAgICAgICAgICAgLy8gVGFraW5nIGFkdmFudGFnZSBvZiB0aGlzIGFuZCBub3Qgd3JpdGluZyBhIFwiZHJhZ1wiIGhhbmRsZXIuXG4gICAgICAgICAgICAgICAgb25VcGRhdGUoe1xuICAgICAgICAgICAgICAgICAgICBub2RlOiBudWxsLFxuICAgICAgICAgICAgICAgICAgICB6b29tOiBldmVudC50cmFuc2Zvcm0uayxcbiAgICAgICAgICAgICAgICAgICAgdHJhbnNsYXRlOiB7IHg6IGV2ZW50LnRyYW5zZm9ybS54LCB5OiBldmVudC50cmFuc2Zvcm0ueSB9LFxuICAgICAgICAgICAgICAgIH0pO1xuICAgICAgICAgICAgICAgIC8vIFRPRE86IHJlbW92ZSB0aGlzPyBTaG91bGRuJ3QgYmUgbXV0YXRpbmcgc3RhdGUga2V5cyBkaXJlY3RseS5cbiAgICAgICAgICAgICAgICB0aGlzLnN0YXRlLmQzLnNjYWxlID0gZXZlbnQudHJhbnNmb3JtLms7XG4gICAgICAgICAgICAgICAgdGhpcy5zdGF0ZS5kMy50cmFuc2xhdGUgPSB7XG4gICAgICAgICAgICAgICAgICAgIHg6IGV2ZW50LnRyYW5zZm9ybS54LFxuICAgICAgICAgICAgICAgICAgICB5OiBldmVudC50cmFuc2Zvcm0ueSxcbiAgICAgICAgICAgICAgICB9O1xuICAgICAgICAgICAgfVxuICAgICAgICB9KSk7XG4gICAgfVxuICAgIC8qKlxuICAgICAqIEFzc2lnbnMgaW50ZXJuYWwgcHJvcGVydGllcyB0aGF0IGFyZSByZXF1aXJlZCBmb3IgdHJlZVxuICAgICAqIG1hbmlwdWxhdGlvbiB0byBlYWNoIG5vZGUgaW4gdGhlIGBkYXRhYCBzZXQgYW5kIHJldHVybnMgYSBuZXcgYGRhdGFgIGFycmF5LlxuICAgICAqXG4gICAgICogQHN0YXRpY1xuICAgICAqL1xuICAgIHN0YXRpYyBhc3NpZ25JbnRlcm5hbFByb3BlcnRpZXMoZGF0YSwgY3VycmVudERlcHRoID0gMCkge1xuICAgICAgICAvLyBXcmFwIHRoZSByb290IG5vZGUgaW50byBhbiBhcnJheSBmb3IgcmVjdXJzaXZlIHRyYW5zZm9ybWF0aW9ucyBpZiBpdCB3YXNuJ3QgaW4gb25lIGFscmVhZHkuXG4gICAgICAgIGNvbnN0IGQgPSBBcnJheS5pc0FycmF5KGRhdGEpID8gZGF0YSA6IFtkYXRhXTtcbiAgICAgICAgcmV0dXJuIGQubWFwKG4gPT4ge1xuICAgICAgICAgICAgY29uc3Qgbm9kZURhdHVtID0gbjtcbiAgICAgICAgICAgIG5vZGVEYXR1bS5fX3JkM3QgPSB7IGlkOiBudWxsLCBkZXB0aDogbnVsbCwgY29sbGFwc2VkOiBmYWxzZSB9O1xuICAgICAgICAgICAgbm9kZURhdHVtLl9fcmQzdC5pZCA9IHV1aWR2NCgpO1xuICAgICAgICAgICAgLy8gRDNAdjUgY29tcGF0OiBtYW51YWxseSBhc3NpZ24gYGRlcHRoYCB0byBub2RlLmRhdGEgc28gd2UgZG9uJ3QgaGF2ZVxuICAgICAgICAgICAgLy8gdG8gaG9sZCBmdWxsIG5vZGUrbGluayBzZXRzIGluIHN0YXRlLlxuICAgICAgICAgICAgLy8gVE9ETzogYXZvaWQgdGhpcyBleHRyYSBzdGVwIGJ5IGNoZWNraW5nIEQzJ3Mgbm9kZS5kZXB0aCBkaXJlY3RseS5cbiAgICAgICAgICAgIG5vZGVEYXR1bS5fX3JkM3QuZGVwdGggPSBjdXJyZW50RGVwdGg7XG4gICAgICAgICAgICAvLyBJZiB0aGVyZSBhcmUgY2hpbGRyZW4sIHJlY3Vyc2l2ZWx5IGFzc2lnbiBwcm9wZXJ0aWVzIHRvIHRoZW0gdG9vLlxuICAgICAgICAgICAgaWYgKG5vZGVEYXR1bS5jaGlsZHJlbiAmJiBub2RlRGF0dW0uY2hpbGRyZW4ubGVuZ3RoID4gMCkge1xuICAgICAgICAgICAgICAgIG5vZGVEYXR1bS5jaGlsZHJlbiA9IFRyZWUuYXNzaWduSW50ZXJuYWxQcm9wZXJ0aWVzKG5vZGVEYXR1bS5jaGlsZHJlbiwgY3VycmVudERlcHRoICsgMSk7XG4gICAgICAgICAgICB9XG4gICAgICAgICAgICByZXR1cm4gbm9kZURhdHVtO1xuICAgICAgICB9KTtcbiAgICB9XG4gICAgLyoqXG4gICAgICogUmVjdXJzaXZlbHkgd2Fsa3MgdGhlIG5lc3RlZCBgbm9kZVNldGAgdW50aWwgYSBub2RlIG1hdGNoaW5nIGBub2RlSWRgIGlzIGZvdW5kLlxuICAgICAqL1xuICAgIGZpbmROb2Rlc0J5SWQobm9kZUlkLCBub2RlU2V0LCBoaXRzKSB7XG4gICAgICAgIGlmIChoaXRzLmxlbmd0aCA+IDApIHtcbiAgICAgICAgICAgIHJldHVybiBoaXRzO1xuICAgICAgICB9XG4gICAgICAgIGhpdHMgPSBoaXRzLmNvbmNhdChub2RlU2V0LmZpbHRlcihub2RlID0+IG5vZGUuX19yZDN0LmlkID09PSBub2RlSWQpKTtcbiAgICAgICAgbm9kZVNldC5mb3JFYWNoKG5vZGUgPT4ge1xuICAgICAgICAgICAgaWYgKG5vZGUuY2hpbGRyZW4gJiYgbm9kZS5jaGlsZHJlbi5sZW5ndGggPiAwKSB7XG4gICAgICAgICAgICAgICAgaGl0cyA9IHRoaXMuZmluZE5vZGVzQnlJZChub2RlSWQsIG5vZGUuY2hpbGRyZW4sIGhpdHMpO1xuICAgICAgICAgICAgfVxuICAgICAgICB9KTtcbiAgICAgICAgcmV0dXJuIGhpdHM7XG4gICAgfVxuICAgIC8qKlxuICAgICAqIFJlY3Vyc2l2ZWx5IHdhbGtzIHRoZSBuZXN0ZWQgYG5vZGVTZXRgIHVudGlsIGFsbCBub2RlcyBhdCBgZGVwdGhgIGhhdmUgYmVlbiBmb3VuZC5cbiAgICAgKlxuICAgICAqIEBwYXJhbSB7bnVtYmVyfSBkZXB0aCBUYXJnZXQgZGVwdGggZm9yIHdoaWNoIG5vZGVzIHNob3VsZCBiZSByZXR1cm5lZFxuICAgICAqIEBwYXJhbSB7YXJyYXl9IG5vZGVTZXQgQXJyYXkgb2YgbmVzdGVkIGBub2RlYCBvYmplY3RzXG4gICAgICogQHBhcmFtIHthcnJheX0gYWNjdW11bGF0b3IgQWNjdW11bGF0b3IgZm9yIG1hdGNoZXMsIHBhc3NlZCBiZXR3ZWVuIHJlY3Vyc2l2ZSBjYWxsc1xuICAgICAqL1xuICAgIGZpbmROb2Rlc0F0RGVwdGgoZGVwdGgsIG5vZGVTZXQsIGFjY3VtdWxhdG9yKSB7XG4gICAgICAgIGFjY3VtdWxhdG9yID0gYWNjdW11bGF0b3IuY29uY2F0KG5vZGVTZXQuZmlsdGVyKG5vZGUgPT4gbm9kZS5fX3JkM3QuZGVwdGggPT09IGRlcHRoKSk7XG4gICAgICAgIG5vZGVTZXQuZm9yRWFjaChub2RlID0+IHtcbiAgICAgICAgICAgIGlmIChub2RlLmNoaWxkcmVuICYmIG5vZGUuY2hpbGRyZW4ubGVuZ3RoID4gMCkge1xuICAgICAgICAgICAgICAgIGFjY3VtdWxhdG9yID0gdGhpcy5maW5kTm9kZXNBdERlcHRoKGRlcHRoLCBub2RlLmNoaWxkcmVuLCBhY2N1bXVsYXRvcik7XG4gICAgICAgICAgICB9XG4gICAgICAgIH0pO1xuICAgICAgICByZXR1cm4gYWNjdW11bGF0b3I7XG4gICAgfVxuICAgIC8qKlxuICAgICAqIFJlY3Vyc2l2ZWx5IHNldHMgdGhlIGludGVybmFsIGBjb2xsYXBzZWRgIHByb3BlcnR5IG9mXG4gICAgICogdGhlIHBhc3NlZCBgVHJlZU5vZGVEYXR1bWAgYW5kIGl0cyBjaGlsZHJlbiB0byBgdHJ1ZWAuXG4gICAgICpcbiAgICAgKiBAc3RhdGljXG4gICAgICovXG4gICAgc3RhdGljIGNvbGxhcHNlTm9kZShub2RlRGF0dW0pIHtcbiAgICAgICAgbm9kZURhdHVtLl9fcmQzdC5jb2xsYXBzZWQgPSB0cnVlO1xuICAgICAgICBpZiAobm9kZURhdHVtLmNoaWxkcmVuICYmIG5vZGVEYXR1bS5jaGlsZHJlbi5sZW5ndGggPiAwKSB7XG4gICAgICAgICAgICBub2RlRGF0dW0uY2hpbGRyZW4uZm9yRWFjaChjaGlsZCA9PiB7XG4gICAgICAgICAgICAgICAgVHJlZS5jb2xsYXBzZU5vZGUoY2hpbGQpO1xuICAgICAgICAgICAgfSk7XG4gICAgICAgIH1cbiAgICB9XG4gICAgLyoqXG4gICAgICogU2V0cyB0aGUgaW50ZXJuYWwgYGNvbGxhcHNlZGAgcHJvcGVydHkgb2ZcbiAgICAgKiB0aGUgcGFzc2VkIGBUcmVlTm9kZURhdHVtYCBvYmplY3QgdG8gYGZhbHNlYC5cbiAgICAgKlxuICAgICAqIEBzdGF0aWNcbiAgICAgKi9cbiAgICBzdGF0aWMgZXhwYW5kTm9kZShub2RlRGF0dW0pIHtcbiAgICAgICAgbm9kZURhdHVtLl9fcmQzdC5jb2xsYXBzZWQgPSBmYWxzZTtcbiAgICB9XG4gICAgLyoqXG4gICAgICogQ29sbGFwc2VzIGFsbCBub2RlcyBpbiBgbm9kZVNldGAgdGhhdCBhcmUgbmVpZ2hib3JzIChzYW1lIGRlcHRoKSBvZiBgdGFyZ2V0Tm9kZWAuXG4gICAgICovXG4gICAgY29sbGFwc2VOZWlnaGJvck5vZGVzKHRhcmdldE5vZGUsIG5vZGVTZXQpIHtcbiAgICAgICAgY29uc3QgbmVpZ2hib3JzID0gdGhpcy5maW5kTm9kZXNBdERlcHRoKHRhcmdldE5vZGUuX19yZDN0LmRlcHRoLCBub2RlU2V0LCBbXSkuZmlsdGVyKG5vZGUgPT4gbm9kZS5fX3JkM3QuaWQgIT09IHRhcmdldE5vZGUuX19yZDN0LmlkKTtcbiAgICAgICAgbmVpZ2hib3JzLmZvckVhY2gobmVpZ2hib3IgPT4gVHJlZS5jb2xsYXBzZU5vZGUobmVpZ2hib3IpKTtcbiAgICB9XG4gICAgLyoqXG4gICAgICogR2VuZXJhdGVzIHRyZWUgZWxlbWVudHMgKGBub2Rlc2AgYW5kIGBsaW5rc2ApIGJ5XG4gICAgICogZ3JhYmJpbmcgdGhlIHJvb3ROb2RlIGZyb20gYHRoaXMuc3RhdGUuZGF0YVswXWAuXG4gICAgICogUmVzdHJpY3RzIHRyZWUgZGVwdGggdG8gYHByb3BzLmluaXRpYWxEZXB0aGAgaWYgZGVmaW5lZCBhbmQgaWYgdGhpcyBpc1xuICAgICAqIHRoZSBpbml0aWFsIHJlbmRlciBvZiB0aGUgdHJlZS5cbiAgICAgKi9cbiAgICBnZW5lcmF0ZVRyZWUoKSB7XG4gICAgICAgIGNvbnN0IHsgaW5pdGlhbERlcHRoLCBkZXB0aEZhY3Rvciwgc2VwYXJhdGlvbiwgbm9kZVNpemUsIG9yaWVudGF0aW9uIH0gPSB0aGlzLnByb3BzO1xuICAgICAgICBjb25zdCB7IGlzSW5pdGlhbFJlbmRlckZvckRhdGFzZXQgfSA9IHRoaXMuc3RhdGU7XG4gICAgICAgIGNvbnN0IHRyZWUgPSBkM3RyZWUoKVxuICAgICAgICAgICAgLm5vZGVTaXplKG9yaWVudGF0aW9uID09PSAnaG9yaXpvbnRhbCcgPyBbbm9kZVNpemUueSwgbm9kZVNpemUueF0gOiBbbm9kZVNpemUueCwgbm9kZVNpemUueV0pXG4gICAgICAgICAgICAuc2VwYXJhdGlvbigoYSwgYikgPT4gYS5wYXJlbnQuZGF0YS5fX3JkM3QuaWQgPT09IGIucGFyZW50LmRhdGEuX19yZDN0LmlkXG4gICAgICAgICAgICA/IHNlcGFyYXRpb24uc2libGluZ3NcbiAgICAgICAgICAgIDogc2VwYXJhdGlvbi5ub25TaWJsaW5ncyk7XG4gICAgICAgIGNvbnN0IHJvb3ROb2RlID0gdHJlZShoaWVyYXJjaHkodGhpcy5zdGF0ZS5kYXRhWzBdLCBkID0+IChkLl9fcmQzdC5jb2xsYXBzZWQgPyBudWxsIDogZC5jaGlsZHJlbikpKTtcbiAgICAgICAgbGV0IG5vZGVzID0gcm9vdE5vZGUuZGVzY2VuZGFudHMoKTtcbiAgICAgICAgY29uc3QgbGlua3MgPSByb290Tm9kZS5saW5rcygpO1xuICAgICAgICAvLyBDb25maWd1cmUgbm9kZXMnIGBjb2xsYXBzZWRgIHByb3BlcnR5IG9uIGZpcnN0IHJlbmRlciBpZiBgaW5pdGlhbERlcHRoYCBpcyBkZWZpbmVkLlxuICAgICAgICBpZiAoaW5pdGlhbERlcHRoICE9PSB1bmRlZmluZWQgJiYgaXNJbml0aWFsUmVuZGVyRm9yRGF0YXNldCkge1xuICAgICAgICAgICAgdGhpcy5zZXRJbml0aWFsVHJlZURlcHRoKG5vZGVzLCBpbml0aWFsRGVwdGgpO1xuICAgICAgICB9XG4gICAgICAgIGlmIChkZXB0aEZhY3Rvcikge1xuICAgICAgICAgICAgbm9kZXMuZm9yRWFjaChub2RlID0+IHtcbiAgICAgICAgICAgICAgICBub2RlLnkgPSBub2RlLmRlcHRoICogZGVwdGhGYWN0b3I7XG4gICAgICAgICAgICB9KTtcbiAgICAgICAgfVxuICAgICAgICByZXR1cm4geyBub2RlcywgbGlua3MgfTtcbiAgICB9XG4gICAgLyoqXG4gICAgICogU2V0IGluaXRpYWwgem9vbSBhbmQgcG9zaXRpb24uXG4gICAgICogQWxzbyBsaW1pdCB6b29tIGxldmVsIGFjY29yZGluZyB0byBgc2NhbGVFeHRlbnRgIG9uIGluaXRpYWwgZGlzcGxheS4gVGhpcyBpcyBuZWNlc3NhcnksXG4gICAgICogYmVjYXVzZSB0aGUgZmlyc3QgdGltZSB3ZSBhcmUgc2V0dGluZyBpdCBhcyBhbiBTVkcgcHJvcGVydHksIGluc3RlYWQgb2YgZ29pbmdcbiAgICAgKiB0aHJvdWdoIEQzJ3Mgc2NhbGluZyBtZWNoYW5pc20sIHdoaWNoIHdvdWxkIGhhdmUgcGlja2VkIHVwIGJvdGggcHJvcGVydGllcy5cbiAgICAgKlxuICAgICAqIEBzdGF0aWNcbiAgICAgKi9cbiAgICBzdGF0aWMgY2FsY3VsYXRlRDNHZW9tZXRyeShuZXh0UHJvcHMpIHtcbiAgICAgICAgbGV0IHNjYWxlO1xuICAgICAgICBpZiAobmV4dFByb3BzLnpvb20gPiBuZXh0UHJvcHMuc2NhbGVFeHRlbnQubWF4KSB7XG4gICAgICAgICAgICBzY2FsZSA9IG5leHRQcm9wcy5zY2FsZUV4dGVudC5tYXg7XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSBpZiAobmV4dFByb3BzLnpvb20gPCBuZXh0UHJvcHMuc2NhbGVFeHRlbnQubWluKSB7XG4gICAgICAgICAgICBzY2FsZSA9IG5leHRQcm9wcy5zY2FsZUV4dGVudC5taW47XG4gICAgICAgIH1cbiAgICAgICAgZWxzZSB7XG4gICAgICAgICAgICBzY2FsZSA9IG5leHRQcm9wcy56b29tO1xuICAgICAgICB9XG4gICAgICAgIHJldHVybiB7XG4gICAgICAgICAgICB0cmFuc2xhdGU6IG5leHRQcm9wcy50cmFuc2xhdGUsXG4gICAgICAgICAgICBzY2FsZSxcbiAgICAgICAgfTtcbiAgICB9XG4gICAgcmVuZGVyKCkge1xuICAgICAgICBjb25zdCB7IG5vZGVzLCBsaW5rcyB9ID0gdGhpcy5nZW5lcmF0ZVRyZWUoKTtcbiAgICAgICAgY29uc3QgeyByZW5kZXJDdXN0b21Ob2RlRWxlbWVudCwgb3JpZW50YXRpb24sIHBhdGhGdW5jLCB0cmFuc2l0aW9uRHVyYXRpb24sIG5vZGVTaXplLCBkZXB0aEZhY3RvciwgaW5pdGlhbERlcHRoLCBzZXBhcmF0aW9uLCBlbmFibGVMZWdhY3lUcmFuc2l0aW9ucywgc3ZnQ2xhc3NOYW1lLCBwYXRoQ2xhc3NGdW5jLCB9ID0gdGhpcy5wcm9wcztcbiAgICAgICAgY29uc3QgeyB0cmFuc2xhdGUsIHNjYWxlIH0gPSB0aGlzLnN0YXRlLmQzO1xuICAgICAgICBjb25zdCBzdWJzY3JpcHRpb25zID0gT2JqZWN0LmFzc2lnbihPYmplY3QuYXNzaWduKE9iamVjdC5hc3NpZ24oe30sIG5vZGVTaXplKSwgc2VwYXJhdGlvbiksIHsgZGVwdGhGYWN0b3IsXG4gICAgICAgICAgICBpbml0aWFsRGVwdGggfSk7XG4gICAgICAgIHJldHVybiAoUmVhY3QuY3JlYXRlRWxlbWVudChcImRpdlwiLCB7IGNsYXNzTmFtZTogXCJyZDN0LXRyZWUtY29udGFpbmVyIHJkM3QtZ3JhYmJhYmxlXCIgfSxcbiAgICAgICAgICAgIFJlYWN0LmNyZWF0ZUVsZW1lbnQoXCJzdHlsZVwiLCBudWxsLCBnbG9iYWxDc3MpLFxuICAgICAgICAgICAgUmVhY3QuY3JlYXRlRWxlbWVudChcInN2Z1wiLCB7IGNsYXNzTmFtZTogYHJkM3Qtc3ZnICR7dGhpcy5zdmdJbnN0YW5jZVJlZn0gJHtzdmdDbGFzc05hbWV9YCwgd2lkdGg6IFwiMTAwJVwiLCBoZWlnaHQ6IFwiMTAwJVwiIH0sXG4gICAgICAgICAgICAgICAgUmVhY3QuY3JlYXRlRWxlbWVudChUcmFuc2l0aW9uR3JvdXBXcmFwcGVyLCB7IGVuYWJsZUxlZ2FjeVRyYW5zaXRpb25zOiBlbmFibGVMZWdhY3lUcmFuc2l0aW9ucywgY29tcG9uZW50OiBcImdcIiwgY2xhc3NOYW1lOiBgcmQzdC1nICR7dGhpcy5nSW5zdGFuY2VSZWZ9YCwgdHJhbnNmb3JtOiBgdHJhbnNsYXRlKCR7dHJhbnNsYXRlLnh9LCR7dHJhbnNsYXRlLnl9KSBzY2FsZSgke3NjYWxlfSlgIH0sXG4gICAgICAgICAgICAgICAgICAgIGxpbmtzLm1hcCgobGlua0RhdGEsIGkpID0+IHtcbiAgICAgICAgICAgICAgICAgICAgICAgIHJldHVybiAoUmVhY3QuY3JlYXRlRWxlbWVudChMaW5rLCB7IGtleTogJ2xpbmstJyArIGksIG9yaWVudGF0aW9uOiBvcmllbnRhdGlvbiwgcGF0aEZ1bmM6IHBhdGhGdW5jLCBwYXRoQ2xhc3NGdW5jOiBwYXRoQ2xhc3NGdW5jLCBsaW5rRGF0YTogbGlua0RhdGEsIG9uQ2xpY2s6IHRoaXMuaGFuZGxlT25MaW5rQ2xpY2tDYiwgb25Nb3VzZU92ZXI6IHRoaXMuaGFuZGxlT25MaW5rTW91c2VPdmVyQ2IsIG9uTW91c2VPdXQ6IHRoaXMuaGFuZGxlT25MaW5rTW91c2VPdXRDYiwgZW5hYmxlTGVnYWN5VHJhbnNpdGlvbnM6IGVuYWJsZUxlZ2FjeVRyYW5zaXRpb25zLCB0cmFuc2l0aW9uRHVyYXRpb246IHRyYW5zaXRpb25EdXJhdGlvbiB9KSk7XG4gICAgICAgICAgICAgICAgICAgIH0pLFxuICAgICAgICAgICAgICAgICAgICBub2Rlcy5tYXAoKGhpZXJhcmNoeVBvaW50Tm9kZSwgaSkgPT4ge1xuICAgICAgICAgICAgICAgICAgICAgICAgY29uc3QgeyBkYXRhLCB4LCB5LCBwYXJlbnQgfSA9IGhpZXJhcmNoeVBvaW50Tm9kZTtcbiAgICAgICAgICAgICAgICAgICAgICAgIHJldHVybiAoUmVhY3QuY3JlYXRlRWxlbWVudChOb2RlLCB7IGtleTogJ25vZGUtJyArIGksIGRhdGE6IGRhdGEsIHBvc2l0aW9uOiB7IHgsIHkgfSwgaGllcmFyY2h5UG9pbnROb2RlOiBoaWVyYXJjaHlQb2ludE5vZGUsIHBhcmVudDogcGFyZW50LCBub2RlQ2xhc3NOYW1lOiB0aGlzLmdldE5vZGVDbGFzc05hbWUocGFyZW50LCBkYXRhKSwgcmVuZGVyQ3VzdG9tTm9kZUVsZW1lbnQ6IHJlbmRlckN1c3RvbU5vZGVFbGVtZW50LCBub2RlU2l6ZTogbm9kZVNpemUsIG9yaWVudGF0aW9uOiBvcmllbnRhdGlvbiwgZW5hYmxlTGVnYWN5VHJhbnNpdGlvbnM6IGVuYWJsZUxlZ2FjeVRyYW5zaXRpb25zLCB0cmFuc2l0aW9uRHVyYXRpb246IHRyYW5zaXRpb25EdXJhdGlvbiwgb25Ob2RlVG9nZ2xlOiB0aGlzLmhhbmRsZU5vZGVUb2dnbGUsIG9uTm9kZUNsaWNrOiB0aGlzLmhhbmRsZU9uTm9kZUNsaWNrQ2IsIG9uTm9kZU1vdXNlT3ZlcjogdGhpcy5oYW5kbGVPbk5vZGVNb3VzZU92ZXJDYiwgb25Ob2RlTW91c2VPdXQ6IHRoaXMuaGFuZGxlT25Ob2RlTW91c2VPdXRDYiwgaGFuZGxlQWRkQ2hpbGRyZW5Ub05vZGU6IHRoaXMuaGFuZGxlQWRkQ2hpbGRyZW5Ub05vZGUsIHN1YnNjcmlwdGlvbnM6IHN1YnNjcmlwdGlvbnMsIGNlbnRlck5vZGU6IHRoaXMuY2VudGVyTm9kZSB9KSk7XG4gICAgICAgICAgICAgICAgICAgIH0pKSkpKTtcbiAgICB9XG59XG5UcmVlLmRlZmF1bHRQcm9wcyA9IHtcbiAgICBvbk5vZGVDbGljazogdW5kZWZpbmVkLFxuICAgIG9uTm9kZU1vdXNlT3ZlcjogdW5kZWZpbmVkLFxuICAgIG9uTm9kZU1vdXNlT3V0OiB1bmRlZmluZWQsXG4gICAgb25MaW5rQ2xpY2s6IHVuZGVmaW5lZCxcbiAgICBvbkxpbmtNb3VzZU92ZXI6IHVuZGVmaW5lZCxcbiAgICBvbkxpbmtNb3VzZU91dDogdW5kZWZpbmVkLFxuICAgIG9uVXBkYXRlOiB1bmRlZmluZWQsXG4gICAgb3JpZW50YXRpb246ICdob3Jpem9udGFsJyxcbiAgICB0cmFuc2xhdGU6IHsgeDogMCwgeTogMCB9LFxuICAgIHBhdGhGdW5jOiAnZGlhZ29uYWwnLFxuICAgIHBhdGhDbGFzc0Z1bmM6IHVuZGVmaW5lZCxcbiAgICB0cmFuc2l0aW9uRHVyYXRpb246IDUwMCxcbiAgICBkZXB0aEZhY3RvcjogdW5kZWZpbmVkLFxuICAgIGNvbGxhcHNpYmxlOiB0cnVlLFxuICAgIGluaXRpYWxEZXB0aDogdW5kZWZpbmVkLFxuICAgIHpvb21hYmxlOiB0cnVlLFxuICAgIGRyYWdnYWJsZTogdHJ1ZSxcbiAgICB6b29tOiAxLFxuICAgIHNjYWxlRXh0ZW50OiB7IG1pbjogMC4xLCBtYXg6IDEgfSxcbiAgICBub2RlU2l6ZTogeyB4OiAxNDAsIHk6IDE0MCB9LFxuICAgIHNlcGFyYXRpb246IHsgc2libGluZ3M6IDEsIG5vblNpYmxpbmdzOiAyIH0sXG4gICAgc2hvdWxkQ29sbGFwc2VOZWlnaGJvck5vZGVzOiBmYWxzZSxcbiAgICBzdmdDbGFzc05hbWU6ICcnLFxuICAgIHJvb3ROb2RlQ2xhc3NOYW1lOiAnJyxcbiAgICBicmFuY2hOb2RlQ2xhc3NOYW1lOiAnJyxcbiAgICBsZWFmTm9kZUNsYXNzTmFtZTogJycsXG4gICAgcmVuZGVyQ3VzdG9tTm9kZUVsZW1lbnQ6IHVuZGVmaW5lZCxcbiAgICBlbmFibGVMZWdhY3lUcmFuc2l0aW9uczogZmFsc2UsXG4gICAgaGFzSW50ZXJhY3RpdmVOb2RlczogZmFsc2UsXG4gICAgZGltZW5zaW9uczogdW5kZWZpbmVkLFxuICAgIGNlbnRlcmluZ1RyYW5zaXRpb25EdXJhdGlvbjogODAwLFxuICAgIGRhdGFLZXk6IHVuZGVmaW5lZCxcbn07XG5leHBvcnQgZGVmYXVsdCBUcmVlO1xuIiwiaW1wb3J0ICogYXMgUmVhY3QgZnJvbSAncmVhY3QnO1xuaW1wb3J0IFRyZWUgZnJvbSAncmVhY3QtZDMtdHJlZSc7XG5pbXBvcnQgeyBMb2NhdGlvbnNDb250ZXh0LCBDb2RlV2l0aEluZm9zLCBEb2N1bWVudFBvc2l0aW9uLCBJbnRlcmFjdGl2ZUNvZGUsIEdvYWxzTG9jYXRpb24sIFBhbmVsV2lkZ2V0UHJvcHMgfSBmcm9tICdAbGVhbnByb3Zlci9pbmZvdmlldyc7XG5pbXBvcnQgdHlwZSB7IFJhd05vZGVEYXR1bSwgQ3VzdG9tTm9kZUVsZW1lbnRQcm9wcyB9IGZyb20gJ3JlYWN0LWQzLXRyZWUvbGliL3R5cGVzL3R5cGVzL2NvbW1vbic7XG5cbmV4cG9ydCB0eXBlIERpc3BsYXlUcmVlID1cbiAgeyBub2RlOiB7IGxhYmVsPzogQ29kZVdpdGhJbmZvcywgbGVuZ3RoOm51bWJlciwgY2hpbGRyZW46IEFycmF5PERpc3BsYXlUcmVlPiB9IH1cblxuZXhwb3J0IHR5cGUgVHJlZU5vZGVEYXR1bSA9IFJhd05vZGVEYXR1bSAmIHsgbGFiZWw/OiBDb2RlV2l0aEluZm9zLCBsZW5ndGg/Om51bWJlciB9XG5cbmV4cG9ydCB0eXBlIERpc3BsYXlUcmVlUHJvcHMgPSBQYW5lbFdpZGdldFByb3BzICYgeyB0cmVlIDogRGlzcGxheVRyZWUgfVxuXG5mdW5jdGlvbiB0cmVlVG9EYXRhKHRyZWU6IERpc3BsYXlUcmVlKTogVHJlZU5vZGVEYXR1bSB7XG4gICAgY29uc3QgeyBsYWJlbCwgbGVuZ3RoLCBjaGlsZHJlbiB9ID0gdHJlZS5ub2RlXG4gICAgaWYgKCFBcnJheS5pc0FycmF5KGNoaWxkcmVuKSkge1xuICAgICAgICB0aHJvdyBuZXcgRXJyb3IoXCJDaGlsZHJlbiBhcmUgbm90IGFuIGFycmF5XCIpXG4gICAgfSAgICBcbiAgICBpZiAoY2hpbGRyZW4ubGVuZ3RoID09IDApIHtcbiAgICAgICAgcmV0dXJuIHtcbiAgICAgICAgICAgIG5hbWU6ICdub2RlJyxcbiAgICAgICAgICAgIGxlbmd0aDogbGVuZ3RoLFxuICAgICAgICAgICAgbGFiZWw6IGxhYmVsXG4gICAgICAgICAgfSAgICAgICAgICBcbiAgICB9IGVsc2Uge1xuICAgICAgICBjb25zdCBjaGlsZHJlbkFzVHJlZXMgPSBjaGlsZHJlbi5tYXAodHJlZVRvRGF0YSlcbiAgICAgICAgcmV0dXJuIHtcbiAgICAgICAgICAgIG5hbWU6ICdub2RlJyxcbiAgICAgICAgICAgIGxlbmd0aDogbGVuZ3RoLFxuICAgICAgICAgICAgbGFiZWw6IGxhYmVsLFxuICAgICAgICAgICAgY2hpbGRyZW46IGNoaWxkcmVuQXNUcmVlc1xuICAgICAgICB9XG4gICAgfSAgXG59XG5cbmZ1bmN0aW9uIHJlbmRlckZvcmVpZ25PYmplY3ROb2RlKHsgbm9kZURhdHVtIH06IEN1c3RvbU5vZGVFbGVtZW50UHJvcHMsIF86IERvY3VtZW50UG9zaXRpb24sXG4gIGZvcmVpZ25PYmplY3RQcm9wczogUmVhY3QuU1ZHUHJvcHM8U1ZHRm9yZWlnbk9iamVjdEVsZW1lbnQ+KTogSlNYLkVsZW1lbnQge1xuICBjb25zdCBub2RlRGF0dW1fID0gbm9kZURhdHVtIGFzIFRyZWVOb2RlRGF0dW1cbiAgY29uc3Qgd2lkdGggPSAxMCAqIChub2RlRGF0dW1fLmxlbmd0aCA/PyAxMClcbiAgcmV0dXJuIChcbiAgICA8Zz5cbiAgICAgIDxyZWN0IHg9XCItNTBcIiB5PVwiLTEwXCIgd2lkdGg9e3dpZHRofSBoZWlnaHQ9XCIyMFwiIGZpbGw9XCJncmVlblwiIHN0eWxlPXt7IGJvcmRlcjogXCJibGFja1wiIH19IC8+XG4gICAgICA8Zm9yZWlnbk9iamVjdCB7Li4uZm9yZWlnbk9iamVjdFByb3BzfSB3aWR0aD17d2lkdGh9IHN0eWxlPXt7IHRleHRBbGlnbjogXCJjZW50ZXJcIiB9fT5cbiAgICAgICAge25vZGVEYXR1bV8ubGFiZWwgJiYgPEludGVyYWN0aXZlQ29kZSBmbXQ9e25vZGVEYXR1bV8ubGFiZWx9IC8+fVxuICAgICAgPC9mb3JlaWduT2JqZWN0PlxuICAgIDwvZz5cbiAgKVxufVxuXG5mdW5jdGlvbiBjZW50ZXJUcmVlIChyIDogUmVhY3QuUmVmT2JqZWN0PEhUTUxEaXZFbGVtZW50PiwgdCA6IGFueSwgc2V0VCA6IFJlYWN0LkRpc3BhdGNoPGFueT4pIHtcbiAgICBSZWFjdC51c2VMYXlvdXRFZmZlY3QoKCkgPT4ge1xuICAgICAgICBjb25zdCBlbHQgPSByLmN1cnJlbnRcbiAgICAgICAgaWYgKGVsdCA9PSBudWxsKSB7IHJldHVybiB9XG4gICAgICAgIGlmICh0ICE9IG51bGwpIHsgcmV0dXJuIH1cbiAgICAgICAgY29uc3QgYiA9IGVsdC5nZXRCb3VuZGluZ0NsaWVudFJlY3QoKVxuICAgICAgICBpZiAoIWIud2lkdGggfHwgIWIuaGVpZ2h0KSB7IHJldHVybiB9XG4gICAgICAgIHNldFQoeyB4OiBiLndpZHRoIC8gMiwgeTogMjAgfSlcbiAgICB9KVxufVxuXG5leHBvcnQgZnVuY3Rpb24gUmVuZGVyRGlzcGxheVRyZWUoeyBwb3MsIHRyZWUsIHIgfTogXG4gICAgeyBwb3M6IERvY3VtZW50UG9zaXRpb24sIHRyZWU6IERpc3BsYXlUcmVlLCByIDogUmVhY3QuUmVmT2JqZWN0PEhUTUxEaXZFbGVtZW50PiB9KTogXG4gICAgSlNYLkVsZW1lbnQge1xuICAgIGNvbnN0IG5vZGVTaXplID0geyB4OiAxMjAsIHk6IDQwIH1cbiAgICBjb25zdCBmb3JlaWduT2JqZWN0UHJvcHMgPSB7IHdpZHRoOiAxMDAsIGhlaWdodDogMzAsIHk6IC0xMCwgeDogLTUwIH1cbiAgICBjb25zdCBbdCwgc2V0VF0gPSBSZWFjdC51c2VTdGF0ZTxhbnkgfCBudWxsPihudWxsKVxuICAgIGNlbnRlclRyZWUociwgdCwgc2V0VClcbiAgICByZXR1cm4gKFxuICAgICAgICA8VHJlZVxuICAgICAgICAgIGRhdGE9e3RyZWVUb0RhdGEodHJlZSl9XG4gICAgICAgICAgdHJhbnNsYXRlPXt0ID8/IHsgeDogMCwgeTogMCB9fVxuICAgICAgICAgIG5vZGVTaXplPXtub2RlU2l6ZX1cbiAgICAgICAgICByZW5kZXJDdXN0b21Ob2RlRWxlbWVudD17cmQzdFByb3BzID0+XG4gICAgICAgICAgICByZW5kZXJGb3JlaWduT2JqZWN0Tm9kZShyZDN0UHJvcHMsIHBvcywgZm9yZWlnbk9iamVjdFByb3BzKX1cbiAgICAgICAgICBvcmllbnRhdGlvbj0ndmVydGljYWwnXG4gICAgICAgICAgcGF0aEZ1bmM9eydzdHJhaWdodCd9IC8+XG4gICAgKVxufVxuXG5leHBvcnQgZGVmYXVsdCBmdW5jdGlvbiBSZW5kZXJEaXNwbGF5KHByb3BzOiBEaXNwbGF5VHJlZVByb3BzKSA6IEpTWC5FbGVtZW50IHtcbiAgICBjb25zdCBwb3MgPSBwcm9wcy5wb3NcbiAgICBjb25zdCBbc2VsZWN0ZWRMb2NzLCBzZXRTZWxlY3RlZExvY3NdID0gUmVhY3QudXNlU3RhdGU8R29hbHNMb2NhdGlvbltdPihbXSk7XG4gICAgY29uc3QgbG9jcyA9IFJlYWN0LnVzZU1lbW8oKCkgPT4gKHtcbiAgICAgICAgaXNTZWxlY3RlZDogKGwgOiBHb2Fsc0xvY2F0aW9uKSA9PiBzZWxlY3RlZExvY3Muc29tZSh2ID0+IEdvYWxzTG9jYXRpb24uaXNFcXVhbCh2LCBsKSksXG4gICAgICAgIHNldFNlbGVjdGVkOiAobCA6IEdvYWxzTG9jYXRpb24sIGFjdCA6IGFueSkgPT4gc2V0U2VsZWN0ZWRMb2NzKGxzID0+IHtcbiAgICAgICAgICAgIC8vIFdlIGVuc3VyZSB0aGF0IGBzZWxlY3RlZExvY3NgIG1haW50YWlucyBpdHMgcmVmZXJlbmNlIGlkZW50aXR5IGlmIHRoZSBzZWxlY3Rpb25cbiAgICAgICAgICAgIC8vIHN0YXR1cyBvZiBgbGAgZGlkbid0IGNoYW5nZS5cbiAgICAgICAgICAgIGNvbnN0IG5ld0xvY3MgPSBscy5maWx0ZXIodiA9PiAhR29hbHNMb2NhdGlvbi5pc0VxdWFsKHYsIGwpKTtcbiAgICAgICAgICAgIGNvbnN0IHdhc1NlbGVjdGVkID0gbmV3TG9jcy5sZW5ndGggIT09IGxzLmxlbmd0aDtcbiAgICAgICAgICAgIGNvbnN0IGlzU2VsZWN0ZWQgPSB0eXBlb2YgYWN0ID09PSAnZnVuY3Rpb24nID8gYWN0KHdhc1NlbGVjdGVkKSA6IGFjdDtcbiAgICAgICAgICAgIGlmIChpc1NlbGVjdGVkKVxuICAgICAgICAgICAgICAgIG5ld0xvY3MucHVzaChsKTtcbiAgICAgICAgICAgIHJldHVybiB3YXNTZWxlY3RlZCA9PT0gaXNTZWxlY3RlZCA/IGxzIDogbmV3TG9jcztcbiAgICAgICAgfSksXG4gICAgICAgIHN1YmV4cHJUZW1wbGF0ZTogeyBtdmFySWQ6ICcnLCBsb2M6IHsgdGFyZ2V0OiAnJyB9fVxuICAgIH0pLCBbc2VsZWN0ZWRMb2NzXSk7XG4gICAgcHJvcHMuc2VsZWN0ZWRMb2NhdGlvbnMgPSBzZWxlY3RlZExvY3M7XG4gICAgUmVhY3QudXNlRWZmZWN0KCgpID0+IHNldFNlbGVjdGVkTG9jcyhbXSksIFtwb3MudXJpLCBwb3MubGluZSwgcG9zLmNoYXJhY3Rlcl0pO1xuICAgIGNvbnN0IHIgPSBSZWFjdC51c2VSZWY8SFRNTERpdkVsZW1lbnQ+KG51bGwpXG4gICAgcmV0dXJuIChcbiAgICA8ZGl2XG4gICAgICBzdHlsZT17e1xuICAgICAgICBoZWlnaHQ6ICc0MDBweCcsXG4gICAgICAgIGRpc3BsYXk6ICdpbmxpbmUtZmxleCcsXG4gICAgICAgIG1pbldpZHRoOiAnNjAwcHgnLFxuICAgICAgICBib3JkZXI6ICcxcHggc29saWQgcmdiYSgxMDAsIDEwMCwgMTAwLCAwLjIpJyxcbiAgICAgICAgb3ZlcmZsb3c6ICdoaWRkZW4nLCBcbiAgICAgICAgcmVzaXplOiAnYm90aCcsXG4gICAgICAgIG9wYWNpdHk6ICcwLjknLFxuICAgICAgfX1cbiAgICAgIHJlZj17cn1cbiAgICA+XG4gICAgIDxMb2NhdGlvbnNDb250ZXh0LlByb3ZpZGVyIHZhbHVlID0ge2xvY3N9PlxuICAgICAgICA8UmVuZGVyRGlzcGxheVRyZWUgcG9zPXtwb3N9IHRyZWU9e3Byb3BzLnRyZWV9IHI9e3J9IC8+XG4gICAgIDwvTG9jYXRpb25zQ29udGV4dC5Qcm92aWRlcj5cbiAgICAgPGRpdj57c2VsZWN0ZWRMb2NzLm1hcChsb2MgPT4ge2NvbnNvbGUubG9nKGxvYyk7IHJldHVybiA8cD5Mb2NhdGlvbiBzZWxlY3RlZDwvcD59KX08L2Rpdj5cbiAgICA8L2Rpdj4pXG59Il0sIm5hbWVzIjpbIk5vZGUiLCJTZWxlY3Rpb24iLCJjb25zdGFudCIsImF0dHJSZW1vdmUiLCJhdHRyUmVtb3ZlTlMiLCJhdHRyQ29uc3RhbnQiLCJhdHRyQ29uc3RhbnROUyIsImF0dHJGdW5jdGlvbiIsImF0dHJGdW5jdGlvbk5TIiwic3R5bGVSZW1vdmUiLCJzdHlsZUNvbnN0YW50Iiwic3R5bGVGdW5jdGlvbiIsInRleHRDb25zdGFudCIsInRleHRGdW5jdGlvbiIsInBhcnNlVHlwZW5hbWVzIiwiZ2V0Iiwic2V0Iiwibm9ldmVudCIsInJnYiIsImNvbG9yUmdiIiwibnVtYmVyIiwiaWRlbnRpdHkiLCJ0aW1lb3V0IiwiaW50ZXJwb2xhdGVUcmFuc2Zvcm0iLCJzdHlsZSIsImVhc2VDdWJpY0luT3V0IiwiZHJhZ0VuYWJsZSIsImhhcyIsInJlYWN0SXNNb2R1bGUiLCJyZXF1aXJlJCQxIiwicmVxdWlyZSQkMCIsInJlcXVpcmUkJDIiLCJyZXF1aXJlJCQzIiwicmVxdWlyZSQkNCIsInByb3BUeXBlc01vZHVsZSIsIl9yZWFjdCIsInJlcXVpcmUkJDUiLCJfaW50ZXJvcFJlcXVpcmVEZWZhdWx0IiwicmVxdWlyZSQkNyIsIlJlYWN0IiwiVHJhbnNpdGlvbkdyb3VwIiwieCIsInBvaW50WCIsInkiLCJwb2ludFkiLCJ1dWlkdjQiLCJ6b29tSWRlbnRpdHkiLCJkZWVwRXF1YWwiLCJfanN4cyIsIl9qc3giXSwibWFwcGluZ3MiOiI7Ozs7Ozs7O0FBQUE7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQWlCQTtBQUNPLElBQUksUUFBUSxHQUFHLFdBQVc7QUFDakMsSUFBSSxRQUFRLEdBQUcsTUFBTSxDQUFDLE1BQU0sSUFBSSxTQUFTLFFBQVEsQ0FBQyxDQUFDLEVBQUU7QUFDckQsUUFBUSxLQUFLLElBQUksQ0FBQyxFQUFFLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQyxHQUFHLFNBQVMsQ0FBQyxNQUFNLEVBQUUsQ0FBQyxHQUFHLENBQUMsRUFBRSxDQUFDLEVBQUUsRUFBRTtBQUM3RCxZQUFZLENBQUMsR0FBRyxTQUFTLENBQUMsQ0FBQyxDQUFDLENBQUM7QUFDN0IsWUFBWSxLQUFLLElBQUksQ0FBQyxJQUFJLENBQUMsRUFBRSxJQUFJLE1BQU0sQ0FBQyxTQUFTLENBQUMsY0FBYyxDQUFDLElBQUksQ0FBQyxDQUFDLEVBQUUsQ0FBQyxDQUFDLEVBQUUsQ0FBQyxDQUFDLENBQUMsQ0FBQyxHQUFHLENBQUMsQ0FBQyxDQUFDLENBQUMsQ0FBQztBQUN6RixTQUFTO0FBQ1QsUUFBUSxPQUFPLENBQUMsQ0FBQztBQUNqQixNQUFLO0FBQ0wsSUFBSSxPQUFPLFFBQVEsQ0FBQyxLQUFLLENBQUMsSUFBSSxFQUFFLFNBQVMsQ0FBQyxDQUFDO0FBQzNDLEVBQUM7QUFrUkQ7QUFDdUIsT0FBTyxlQUFlLEtBQUssVUFBVSxHQUFHLGVBQWUsR0FBRyxVQUFVLEtBQUssRUFBRSxVQUFVLEVBQUUsT0FBTyxFQUFFO0FBQ3ZILElBQUksSUFBSSxDQUFDLEdB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Q0FBQyxDQUFDLFFBQVEsRUFBRSxDQUFDLENBQUMsUUFBUSxDQUFDLEdBQUcsQ0FBQyxDQUFDLEdBQUcsQ0FBQyxDQUFDLENBQUM7QUFDOUQsR0FBRztBQUNIO0FBQ0EsRUFBRSxLQUFLLElBQUksTUFBTSxHQUFHLElBQUksQ0FBQyxPQUFPLEVBQUUsQ0FBQyxHQUFHLE1BQU0sQ0FBQyxNQUFNLEVBQUUsVUFBVSxHQUFHLElBQUksS0FBSyxDQUFDLENBQUMsQ0FBQyxFQUFFLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQyxHQUFHLENBQUMsRUFBRSxFQUFFLENBQUMsRUFBRTtBQUNuRyxJQUFJLEtBQUssSUFBSSxLQUFLLEdBQUcsTUFBTSxDQUFDLENBQUMsQ0FBQyxFQUFFLENBQUMsR0FBRyxLQUFLLENBQUMsTUFBTSxFQUFFLFNBQVMsR0FBRyxVQUFVLENBQUMsQ0FBQyxDQUFDLEdBQUcsSUFBSSxLQUFLLENBQUMsQ0FBQyxDQUFDLEVBQUUsSUFBSSxFQUFFLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQyxHQUFHLENBQUMsRUFBRSxFQUFFLENBQUMsRUFBRTtBQUNySCxNQUFNLElBQUksSUFBSSxHQUFHLEtBQUssQ0FBQyxDQUFDLENBQUMsRUFBRTtBQUMzQixRQUFRLFNBQVMsQ0FBQyxDQUFDLENBQUMsR0FBRyxJQUFJLENBQUM7QUFDNUIsT0FBTztBQUNQLEtBQUs7QUFDTCxJQUFJLFNBQVMsQ0FBQyxJQUFJLENBQUMsV0FBVyxDQUFDLENBQUM7QUFDaEMsR0FBRztBQUNIO0FBQ0EsRUFBRSxPQUFPLElBQUlBLFdBQVMsQ0FBQyxVQUFVLEVBQUUsSUFBSSxDQUFDLFFBQVEsQ0FBQyxDQUFDLEtBQUssRUFBRSxDQUFDO0FBQzFELENBQUM7QUFDRDtBQUNBLFNBQVMsU0FBUyxDQUFDLENBQUMsRUFBRSxDQUFDLEVBQUU7QUFDekIsRUFBRSxPQUFPLENBQUMsR0FBRyxDQUFDLEdBQUcsQ0FBQyxDQUFDLEdBQUcsQ0FBQyxHQUFHLENBQUMsR0FBRyxDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsR0FBRyxDQUFDLEdBQUcsR0FBRyxDQUFDO0FBQ25EOztBQ3ZCZSx1QkFBUSxHQUFHO0FBQzFCLEVBQUUsSUFBSSxRQUFRLEdBQUcsU0FBUyxDQUFDLENBQUMsQ0FBQyxDQUFDO0FBQzlCLEVBQUUsU0FBUyxDQUFDLENBQUMsQ0FBQyxHQUFHLElBQUksQ0FBQztBQUN0QixFQUFFLFFBQVEsQ0FBQyxLQUFLLENBQUMsSUFBSSxFQUFFLFNBQVMsQ0FBQyxDQUFDO0FBQ2xDLEVBQUUsT0FBTyxJQUFJLENBQUM7QUFDZDs7QUNMZSx3QkFBUSxHQUFHO0FBQzFCLEVBQUUsT0FBTyxLQUFLLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxDQUFDO0FBQzFCOztBQ0ZlLHVCQUFRLEdBQUc7QUFDMUI7QUFDQSxFQUFFLEtBQUssSUFBSSxNQUFNLEdBQUcsSUFBSSxDQUFDLE9BQU8sRUFBRSxDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUMsR0FBRyxNQUFNLENBQUMsTUFBTSxFQUFFLENBQUMsR0FBRyxDQUFDLEVBQUUsRUFBRSxDQUFDLEVBQUU7QUFDeEUsSUFBSSxLQUFLLElBQUksS0FBSyxHQUFHLE1BQU0sQ0FBQyxDQUFDLENBQUMsRUFBRSxDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUMsR0FBRyxLQUFLLENBQUMsTUFBTSxFQUFFLENBQUMsR0FBRyxDQUFDLEVBQUUsRUFBRSxDQUFDLEVBQUU7QUFDckUsTUFBTSxJQUFJLElBQUksR0FBRyxLQUFLLENBQUMsQ0FBQyxDQUFDLENBQUM7QUFDMUIsTUFBTSxJQUFJLElBQUksRUFBRSxPQUFPLElBQUksQ0FBQztBQUM1QixLQUFLO0FBQ0wsR0FBRztBQUNIO0FBQ0EsRUFBRSxPQUFPLElBQUksQ0FBQztBQUNkOztBQ1ZlLHVCQUFRLEdBQUc7QUFDMUIsRUFBRSxJQUFJLElBQUksR0FBRyxDQUFDLENBQUM7QUFDZixFQUFFLEtBQUssTUFBTSxJQUFJLElBQUksSUFBSSxFQUFFLEVBQUUsSUFBSSxDQUFDO0FBQ2xDLEVBQUUsT0FBTyxJQUFJLENBQUM7QUFDZDs7QUNKZSx3QkFBUSxHQUFHO0FBQzFCLEVBQUUsT0FBTyxDQUFDLElBQUksQ0FBQyxJQUFJLEVBQUUsQ0FBQztBQUN0Qjs7QUNGZSx1QkFBUSxDQUFDLFFBQVEsRUFBRTtBQUNsQztBQUNBLEVBQUUsS0FBSyxJQUFJLE1BQU0sR0FBRyxJQUFJLENBQUMsT0FBTyxFQUFFLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQyxHQUFHLE1BQU0sQ0FBQyxNQUFNLEVBQUUsQ0FBQyxHQUFHLENBQUMsRUFBRSxFQUFFLENBQUMsRUFBRTtBQUN4RSxJQUFJLEtBQUssSUFBSSxLQUFLLEdBQUcsTUFBTSxDQUFDLENBQUMsQ0FBQyxFQUFFLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQyxHQUFHLEtBQUssQ0FBQyxNQUFNLEVBQUUsSUFBSSxFQUFFLENBQUMsR0FBRyxDQUFDLEVBQUUsRUFBRSxDQUFDLEVBQUU7QUFDM0UsTUFBTSxJQUFJLElBQUksR0FBRyxLQUFLLENBQUMsQ0FBQyxDQUFDLEVBQUUsUUFBUSxDQUFDLElBQUksQ0FBQyxJQUFJLEVBQUUsSUFBSSxDQUFDLFFBQVEsRUFBRSxDQUFDLEVBQUUsS0FBSyxDQUFDLENBQUM7QUFDeEUsS0FBSztBQUNMLEdBQUc7QUFDSDtBQUNBLEVBQUUsT0FBTyxJQUFJLENBQUM7QUFDZDs7QUNQQSxTQUFTRSxZQUFVLENBQUMsSUFBSSxFQUFFO0FBQzFCLEVBQUUsT0FBTyxXQUFXO0FBQ3BCLElBQUksSUFBSSxDQUFDLGVBQWUsQ0FBQyxJQUFJLENBQUMsQ0FBQztBQUMvQixHQUFHLENBQUM7QUFDSixDQUFDO0FBQ0Q7QUFDQSxTQUFTQyxjQUFZLENBQUMsUUFBUSxFQUFFO0FBQ2hDLEVBQUUsT0FBTyxXQUFXO0FBQ3BCLElBQUksSUFBSSxDQUFDLGlCQUFpQixDQUFDLFFBQVEsQ0FBQyxLQUFLLEVBQUUsUUFBUSxDQUFDLEtBQUssQ0FBQyxDQUFDO0FBQzNELEdBQUcsQ0FBQztBQUNKLENBQUM7QUFDRDtBQUNBLFNBQVNDLGNBQVksQ0FBQyxJQUFJLEVBQUUsS0FBSyxFQUFFO0FBQ25DLEVBQUUsT0FBTyxXQUFXO0FBQ3BCLElBQUksSUFBSSxDQUFDLFlBQVksQ0FBQyxJQUFJLEVBQUUsS0FBSyxDQUFDLENBQUM7QUFDbkMsR0FBRyxDQUFDO0FBQ0osQ0FBQztBQUNEO0FBQ0EsU0FBU0MsZ0JBQWMsQ0FBQyxRQUFRLEVBQUUsS0FBSyxFQUFFO0FBQ3pDLEVBQUUsT0FBTyxXQUFXO0FBQ3BCLElBQUksSUFBSSxDQUFDLGNBQWMsQ0FBQyxRQUFRLENBQUMsS0FBSyxFQUFFLFFBQVEsQ0FBQyxLQUFLLEVBQUUsS0FBSyxDQUFDLENBQUM7QUFDL0QsR0FBRyxDQUFDO0FBQ0osQ0FBQztBQUNEO0FBQ0EsU0FBU0MsY0FBWSxDQUFDLElBQUksRUFBRSxLQUFLLEVBQUU7QUFDbkMsRUFBRSxPQUFPLFdBQVc7QUFDcEIsSUFBSSxJQUFJLENBQUMsR0FBRyxLQUFLLENBQUMsS0FBSyxDQUFDLElBQUksRUFBRSxTQUFTLENBQUMsQ0FBQztBQUN6QyxJQUFJLElBQUksQ0FBQyxJQUFJLElBQUksRUFBRSxJQUFJLENBQUMsZUFBZSxDQUFDLElBQUksQ0FBQyxDQUFDO0FBQzlDLFNBQVMsSUFBSSxDQUFDLFlBQVksQ0FBQyxJQUFJLEVBQUUsQ0FBQyxDQUFDLENBQUM7QUFDcEMsR0FBRyxDQUFDO0FBQ0osQ0FBQztBQUNEO0FBQ0EsU0FBU0MsZ0JBQWMsQ0FBQyxRQUFRLEVBQUUsS0FBSyxFQUFFO0FBQ3pDLEVBQUUsT0FBTyxXQUFXO0FBQ3BCLElBQUksSUFBSSxDQUFDLEdBQUcsS0FBSyxDQUFDLEtBQUssQ0FBQyxJQUFJLEVBQUUsU0FBUyxDQUFDLENBQUM7QUFDekMsSUFBSSxJQUFJLENBQUMsSUFBSSxJQUFJLEVBQUUsSUFBSSxDQUFDLGlCQUFpQixDQUFDLFFBQVEsQ0FBQyxLQUFLLEVBQUUsUUFBUSxDQUFDLEtBQUssQ0FBQyxDQUFDO0FBQzFFLFNBQVMsSUFBSSxDQUFDLGNBQWMsQ0FBQyxRQUFRLENBQUMsS0FBSyxFQUFFLFFBQVEsQ0FBQyxLQUFLLEVBQUUsQ0FBQyxDQUFDLENBQUM7QUFDaEUsR0FBRyxDQUFDO0FBQ0osQ0FBQztBQUNEO0FBQ2UsdUJBQVEsQ0FBQyxJQUFJLEVBQUUsS0FBSyxFQUFFO0FBQ3JDLEVBQUUsSUFBSSxRQUFRLEdBQUcsU0FBUyxDQUFDLElBQUksQ0FBQyxDQUFDO0FBQ2pDO0FBQ0EsRUFBRSxJQUFJLFNBQVMsQ0FBQyxNQUFNLEdBQUcsQ0FBQyxFQUFFO0FBQzVCLElBQUksSUFBSSxJQUFJLEdBQUcsSUFBSSxDQUFDLElBQUksRUFBRSxDQUFDO0FBQzNCLElBQUksT0FBTyxRQUFRLENBQUMsS0FBSztBQUN6QixVQUFVLElBQUksQ0FBQyxjQUFjLENBQUMsUUFBUSxDQUFDLEtBQUssRUFBRSxRQUFRLENBQUMsS0FBSyxDQUFDO0FBQzdELFVBQVUsSUFBSSxDQUFDLFlBQVksQ0FBQyxRQUFRLENBQUMsQ0FBQztBQUN0QyxHQUFHO0FBQ0g7QUFDQSxFQUFFLE9BQU8sSUFBSSxDQUFDLElBQUksQ0FBQyxDQUFDLEtBQUssSUFBSSxJQUFJO0FBQ2pDLFNBQVMsUUFBUSxDQUFDLEtBQUssR0FBR0osY0FBWSxHQUFHRCxZQUFVLEtBQUssT0FBTyxLQUFLLEtBQUssVUFBVTtBQUNuRixTQUFTLFFBQVEsQ0FBQyxLQUFLLEdBQUdLLGdCQUFjLEdBQUdELGNBQVk7QUFDdkQsU0FBUyxRQUFRLENBQUMsS0FBSyxHQUFHRCxnQkFBYyxHQUFHRCxjQUFZLENBQUMsQ0FBQyxFQUFFLFFBQVEsRUFBRSxLQUFLLENBQUMsQ0FBQyxDQUFDO0FBQzdFOztBQ3hEZSxvQkFBUSxDQUFDLElBQUksRUFBRTtBQUM5QixFQUFFLE9BQU8sQ0FBQyxJQUFJLENBQUMsYUFBYSxJQUFJLElBQUksQ0FBQyxhQUFhLENBQUMsV0FBVztBQUM5RCxVQUFVLElBQUksQ0FBQyxRQUFRLElBQUksSUFBSSxDQUFDO0FBQ2hDLFNBQVMsSUFBSSxDQUFDLFdBQVcsQ0FBQztBQUMxQjs7QUNGQSxTQUFTSSxhQUFXLENBQUMsSUFBSSxFQUFFO0FBQzNCLEVBQUUsT0FBTyxXQUFXO0FBQ3BCLElBQUksSUFBSSxDQUFDLEtBQUssQ0FBQyxjQUFjLENBQUMsSUFBSSxDQUFDLENBQUM7QUFDcEMsR0FBRyxDQUFDO0FBQ0osQ0FBQztBQUNEO0FBQ0EsU0FBU0MsZUFBYSxDQUFDLElBQUksRUFBRSxLQUFLLEVBQUUsUUFBUSxFQUFFO0FBQzlDLEVBQUUsT0FBTyxXQUFXO0FBQ3BCLElBQUksSUFBSSxDQUFDLEtBQUssQ0FBQyxXQUFXLENBQUMsSUFBSSxFQUFFLEtBQUssRUFBRSxRQUFRLENBQUMsQ0FBQztBQUNsRCxHQUFHLENBQUM7QUFDSixDQUFDO0FBQ0Q7QUFDQSxTQUFTQyxlQUFhLENBQUMsSUFBSSxFQUFFLEtBQUssRUFBRSxRQUFRLEVBQUU7QUFDOUMsRUFBRSxPQUFPLFdBQVc7QUFDcEIsSUFBSSxJQUFJLENBQUMsR0FBRyxLQUFLLENBQUMsS0FBSyxDQUFDLElBQUksRUFBRSxTQUFTLENBQUMsQ0FBQztBQUN6QyxJQUFJLElBQUksQ0FBQyxJQUFJLElBQUksRUFBRSxJQUFJLENBQUMsS0FBSyxDQUFDLGNBQWMsQ0FBQyxJQUFJLENBQUMsQ0FBQztBQUNuRCxTQUFTLElBQUksQ0FBQyxLQUFLLENBQUMsV0FBVyxDQUFDLElBQUksRUFBRSxDQUFDLEVBQUUsUUFBUSxDQUFDLENBQUM7QUFDbkQsR0FBRyxDQUFDO0FBQ0osQ0FBQztBQUNEO0FBQ2Usd0JBQVEsQ0FBQyxJQUFJLEVBQUUsS0FBSyxFQUFFLFFBQVEsRUFBRTtBQUMvQyxFQUFFLE9BQU8sU0FBUyxDQUFDLE1BQU0sR0FBRyxDQUFDO0FBQzdCLFFBQVEsSUFBSSxDQUFDLElBQUksQ0FBQyxDQUFDLEtBQUssSUFBSSxJQUFJO0FBQ2hDLGNBQWNGLGFBQVcsR0FBRyxPQUFPLEtBQUssS0FBSyxVQUFVO0FBQ3ZELGNBQWNFLGVBQWE7QUFDM0IsY0FBY0QsZUFBYSxFQUFFLElBQUksRUFBRSxLQUFLLEVBQUUsUUFBUSxJQUFJLElBQUksR0FBRyxFQUFFLEdBQUcsUUFBUSxDQUFDLENBQUM7QUFDNUUsUUFBUSxVQUFVLENBQUMsSUFBSSxDQUFDLElBQUksRUFBRSxFQUFFLElBQUksQ0FBQyxDQUFDO0FBQ3RDLENBQUM7QUFDRDtBQUNPLFNBQVMsVUFBVSxDQUFDLElBQUksRUFBRSxJQUFJLEVBQUU7QUFDdkMsRUFBRSxPQUFPLElBQUksQ0FBQyxLQUFLLENBQUMsZ0JBQWdCLENBQUMsSUFBSSxDQUFDO0FBQzFDLFNBQVMsV0FBVyxDQUFDLElBQUksQ0FBQyxDQUFDLGdCQUFnQixDQUFDLElBQUksRUFBRSxJQUFJLENBQUMsQ0FBQyxnQkFBZ0IsQ0FBQyxJQUFJLENBQUMsQ0FBQztBQUMvRTs7QUNsQ0EsU0FBUyxjQUFjLENBQUMsSUFBSSxFQUFFO0FBQzlCLEVBQUUsT0FBTyxXQUFXO0FBQ3BCLElBQUksT0FBTyxJQUFJLENBQUMsSUFBSSxDQUFDLENBQUM7QUFDdEIsR0FBRyxDQUFDO0FBQ0osQ0FBQztBQUNEO0FBQ0EsU0FBUyxnQkFBZ0IsQ0FBQyxJQUFJLEVBQUUsS0FBSyxFQUFFO0FBQ3ZDLEVBQUUsT0FBTyxXQUFXO0FBQ3BCLElBQUksSUFBSSxDQUFDLElBQUksQ0FBQyxHQUFHLEtBQUssQ0FBQztBQUN2QixHQUFHLENBQUM7QUFDSixDQUFDO0FBQ0Q7QUFDQSxTQUFTLGdCQUFnQixDQUFDLElBQUksRUFBRSxLQUFLLEVBQUU7QUFDdkMsRUFBRSxPQUFPLFdBQVc7QUFDcEIsSUFBSSxJQUFJLENBQUMsR0FBRyxLQUFLLENBQUMsS0FBSyxDQUFDLElBQUksRUFBRSxTQUFTLENBQUMsQ0FBQztBQUN6QyxJQUFJLElBQUksQ0FBQyxJQUFJLElBQUksRUFBRSxPQUFPLElBQUksQ0FBQyxJQUFJLENBQUMsQ0FBQztBQUNyQyxTQUFTLElBQUksQ0FBQyxJQUFJLENBQUMsR0FBRyxDQUFDLENBQUM7QUFDeEIsR0FBRyxDQUFDO0FBQ0osQ0FBQztBQUNEO0FBQ2UsMkJBQVEsQ0FBQyxJQUFJLEVBQUUsS0FBSyxFQUFFO0FBQ3JDLEVBQUUsT0FBTyxTQUFTLENBQUMsTUFBTSxHQUFHLENBQUM7QUFDN0IsUUFBUSxJQUFJLENBQUMsSUFBSSxDQUFDLENBQUMsS0FBSyxJQUFJLElBQUk7QUFDaEMsWUFBWSxjQUFjLEdBQUcsT0FBTyxLQUFLLEtBQUssVUFBVTtBQUN4RCxZQUFZLGdCQUFnQjtBQUM1QixZQUFZLGdCQUFnQixFQUFFLElBQUksRUFBRSxLQUFLLENBQUMsQ0FBQztBQUMzQyxRQUFRLElBQUksQ0FBQyxJQUFJLEVBQUUsQ0FBQyxJQUFJLENBQUMsQ0FBQztBQUMxQjs7QUMzQkEsU0FBUyxVQUFVLENBQUMsTUFBTSxFQUFFO0FBQzVCLEVBQUUsT0FBTyxNQUFNLENBQUMsSUFBSSxFQUFFLENBQUMsS0FBSyxDQUFDLE9BQU8sQ0FBQyxDQUFDO0FBQ3RDLENBQUM7QUFDRDtBQUNBLFNBQVMsU0FBUyxDQUFDLElBQUksRUFBRTtBQUN6QixFQUFFLE9BQU8sSUFBSSxDQUFDLFNBQVMsSUFBSSxJQUFJLFNBQVMsQ0FBQyxJQUFJLENBQUMsQ0FBQztBQUMvQyxDQUFDO0FBQ0Q7QUFDQSxTQUFTLFNBQVMsQ0FBQyxJQUFJLEVBQUU7QUFDekIsRUFBRSxJQUFJLENBQUMsS0FBSyxHQUFHLElBQUksQ0FBQztBQUNwQixFQUFFLElBQUksQ0FBQyxNQUFNLEdBQUcsVUFBVSxDQUFDLElBQUksQ0FBQyxZQUFZLENBQUMsT0FBTyxDQUFDLElBQUksRUFBRSxDQUFDLENBQUM7QUFDN0QsQ0FBQztBQUNEO0FBQ0EsU0FBUyxDQUFDLFNBQVMsR0FBRztBQUN0QixFQUFFLEdBQUcsRUFBRSxTQUFTLElBQUksRUFBRTtBQUN0QixJQUFJLElBQUksQ0FBQyxHQUFHLElBQUksQ0FBQyxNQUFNLENBQUMsT0FBTyxDQUFDLElBQUksQ0FBQyxDQUFDO0FBQ3RDLElBQUksSUFBSSxDQUFDLEdBQUcsQ0FBQyxFQUFFO0FBQ2YsTUFBTSxJQUFJLENBQUMsTUFBTSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsQ0FBQztBQUM3QixNQUFNLElBQUksQ0FBQyxLQUFLLENBQUMsWUFBWSxDQUFDLE9BQU8sRUFBRSxJQUFJLENBQUMsTUFBTSxDQUFDLElBQUksQ0FBQyxHQUFHLENBQUMsQ0FBQyxDQUFDO0FBQzlELEtBQUs7QUFDTCxHQUFHO0FBQ0gsRUFBRSxNQUFNLEVBQUUsU0FBUyxJQUFJLEVBQUU7QUFDekIsSUFBSSxJQUFJLENBQUMsR0FBRyxJQUFJLENBQUMsTUFBTSxDQUFDLE9BQU8sQ0FBQyxJQUFJLENBQUMsQ0FBQztBQUN0QyxJQUFJLElBQUksQ0FBQyxJQUFJLENBQUMsRUFBRTtBQUNoQixNQUFNLElBQUksQ0FBQyxNQUFNLENBQUMsTUFBTSxDQUFDLENBQUMsRUFBRSxDQUFDLENBQUMsQ0FBQztBQUMvQixNQUFNLElBQUksQ0FBQyxLQUFLLENBQUMsWUFBWSxDQUFDLE9BQU8sRUFBRSxJQUFJLENBQUMsTUFBTSxDQUFDLElBQUksQ0FBQyxHQUFHLENBQUMsQ0FBQyxDQUFDO0FBQzlELEtBQUs7QUFDTCxHQUFHO0FBQ0gsRUFBRSxRQUFRLEVBQUUsU0FBUyxJQUFJLEVBQUU7QUFDM0IsSUFBSSxPQUFPLElBQUksQ0FBQyxNQUFNLENBQUMsT0FBTyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsQ0FBQztBQUMxQyxHQUFHO0FBQ0gsQ0FBQyxDQUFDO0FBQ0Y7QUFDQSxTQUFTLFVBQVUsQ0FBQyxJQUFJLEVBQUUsS0FBSyxFQUFFO0FBQ2pDLEVBQUUsSUFBSSxJQUFJLEdBQUcsU0FBUyxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUMsR0FBRyxDQUFDLENBQUMsRUFBRSxDQUFDLEdBQUcsS0FBSyxDQUFDLE1BQU0sQ0FBQztBQUN2RCxFQUFFLE9BQU8sRUFBRSxDQUFDLEdBQUcsQ0FBQyxFQUFFLElBQUksQ0FBQyxHQUFHLENBQUMsS0FBSyxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUM7QUFDckMsQ0FBQztBQUNEO0FBQ0EsU0FBUyxhQUFhLENBQUMsSUFBSSxFQUFFLEtBQUssRUFBRTtBQUNwQyxFQUFFLElBQUksSUFBSSxHQUFHLFNBQVMsQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDLEdBQUcsQ0FBQyxDQUFDLEVBQUUsQ0FBQyxHQUFHLEtBQUssQ0FBQyxNQUFNLENBQUM7QUFDdkQsRUFBRSxPQUFPLEVBQUUsQ0FBQyxHQUFHLENBQUMsRUFBRSxJQUFJLENBQUMsTUFBTSxDQUFDLEtBQUssQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDO0FBQ3hDLENBQUM7QUFDRDtBQUNBLFNBQVMsV0FBVyxDQUFDLEtBQUssRUFBRTtBQUM1QixFQUFFLE9BQU8sV0FBVztBQUNwQixJQUFJLFVBQVUsQ0FBQyxJQUFJLEVBQUUsS0FBSyxDQUFDLENBQUM7QUFDNUIsR0FBRyxDQUFDO0FBQ0osQ0FBQztBQUNEO0FBQ0EsU0FBUyxZQUFZLENBQUMsS0FBSyxFQUFFO0FBQzdCLEVBQUUsT0FBTyxXQUFXO0FBQ3BCLElBQUksYUFBYSxDQUFDLElBQUksRUFBRSxLQUFLLENBQUMsQ0FBQztBQUMvQixHQUFHLENBQUM7QUFDSixDQUFDO0FBQ0Q7QUFDQSxTQUFTLGVBQWUsQ0FBQyxLQUFLLEVBQUUsS0FBSyxFQUFFO0FBQ3ZDLEVBQUUsT0FBTyxXQUFXO0FBQ3BCLElBQUksQ0FBQyxLQUFLLENBQUMsS0FBSyxDQUFDLElBQUksRUFBRSxTQUFTLENBQUMsR0FBRyxVQUFVLEdBQUcsYUFBYSxFQUFFLElBQUksRUFBRSxLQUFLLENBQUMsQ0FBQztBQUM3RSxHQUFHLENBQUM7QUFDSixDQUFDO0FBQ0Q7QUFDZSwwQkFBUSxDQUFDLElBQUksRUFBRSxLQUFLLEVBQUU7QUFDckMsRUFBRSxJQUFJLEtBQUssR0FBRyxVQUFVLENBQUMsSUFBSSxHQUFHLEVBQUUsQ0FBQyxDQUFDO0FBQ3BDO0FBQ0EsRUFBRSxJQUFJLFNBQVMsQ0FBQyxNQUFNLEdBQUcsQ0FBQyxFQUFFO0FBQzVCLElBQUksSUFBSSxJQUFJLEdBQUcsU0FBUyxDQUFDLElBQUksQ0FBQyxJQUFJLEVBQUUsQ0FBQyxFQUFFLENBQUMsR0FBRyxDQUFDLENBQUMsRUFBRSxDQUFDLEdBQUcsS0FBSyxDQUFDLE1BQU0sQ0FBQztBQUNoRSxJQUFJLE9BQU8sRUFBRSxDQUFDLEdBQUcsQ0FBQyxFQUFFLElBQUksQ0FBQyxJQUFJLENBQUMsUUFBUSxDQUFDLEtBQUssQ0FBQyxDQUFDLENBQUMsQ0FBQyxFQUFFLE9BQU8sS0FBSyxDQUFDO0FBQy9ELElBQUksT0FBTyxJQUFJLENBQUM7QUFDaEIsR0FBRztBQUNIO0FBQ0EsRUFBRSxPQUFPLElBQUksQ0FBQyxJQUFJLENBQUMsQ0FBQyxPQUFPLEtBQUssS0FBSyxVQUFVO0FBQy9DLFFBQVEsZUFBZSxHQUFHLEtBQUs7QUFDL0IsUUFBUSxXQUFXO0FBQ25CLFFBQVEsWUFBWSxFQUFFLEtBQUssRUFBRSxLQUFLLENBQUMsQ0FBQyxDQUFDO0FBQ3JDOztBQzFFQSxTQUFTLFVBQVUsR0FBRztBQUN0QixFQUFFLElBQUksQ0FBQyxXQUFXLEdBQUcsRUFBRSxDQUFDO0FBQ3hCLENBQUM7QUFDRDtBQUNBLFNBQVNFLGNBQVksQ0FBQyxLQUFLLEVBQUU7QUFDN0IsRUFBRSxPQUFPLFdBQVc7QUFDcEIsSUFBSSxJQUFJLENBQUMsV0FBVyxHQUFHLEtBQUssQ0FBQztBQUM3QixHQUFHLENBQUM7QUFDSixDQUFDO0FBQ0Q7QUFDQSxTQUFTQyxjQUFZLENBQUMsS0FBSyxFQUFFO0FBQzdCLEVBQUUsT0FBTyxXQUFXO0FBQ3BCLElBQUksSUFBSSxDQUFDLEdBQUcsS0FBSyxDQUFDLEtBQUssQ0FBQyxJQUFJLEVBQUUsU0FBUyxDQUFDLENBQUM7QUFDekMsSUFBSSxJQUFJLENBQUMsV0FBVyxHQUFHLENBQUMsSUFBSSxJQUFJLEdBQUcsRUFBRSxHQUFHLENBQUMsQ0FBQztBQUMxQyxHQUFHLENBQUM7QUFDSixDQUFDO0FBQ0Q7QUFDZSx1QkFBUSxDQUFDLEtBQUssRUFBRTtBQUMvQixFQUFFLE9BQU8sU0FBUyxDQUFDLE1BQU07QUFDekIsUUFBUSxJQUFJLENBQUMsSUFBSSxDQUFDLEtBQUssSUFBSSxJQUFJO0FBQy9CLFlBQVksVUFBVSxHQUFHLENBQUMsT0FBTyxLQUFLLEtBQUssVUFBVTtBQUNyRCxZQUFZQSxjQUFZO0FBQ3hCLFlBQVlELGNBQVksRUFBRSxLQUFLLENBQUMsQ0FBQztBQUNqQyxRQUFRLElBQUksQ0FBQyxJQUFJLEVBQUUsQ0FBQyxXQUFXLENBQUM7QUFDaEM7O0FDeEJBLFNBQVMsVUFBVSxHQUFHO0FBQ3RCLEVBQUUsSUFBSSxDQUFDLFNBQVMsR0FBRyxFQUFFLENBQUM7QUFDdEIsQ0FBQztBQUNEO0FBQ0EsU0FBUyxZQUFZLENBQUMsS0FBSyxFQUFFO0FBQzdCLEVBQUUsT0FBTyxXQUFXO0FBQ3BCLElBQUksSUFBSSxDQUFDLFNBQVMsR0FBRyxLQUFLLENBQUM7QUFDM0IsR0FBRyxDQUFDO0FBQ0osQ0FBQztBQUNEO0FBQ0EsU0FBUyxZQUFZLENBQUMsS0FBSyxFQUFFO0FBQzdCLEVBQUUsT0FBTyxXQUFXO0FBQ3BCLElBQUksSUFBSSxDQUFDLEdBQUcsS0FBSyxDQUFDLEtBQUssQ0FBQyxJQUFJLEVBQUUsU0FBUyxDQUFDLENBQUM7QUFDekMsSUFBSSxJQUFJLENBQUMsU0FBUyxHQUFHLENBQUMsSUFBSSxJQUFJLEdBQUcsRUFBRSxHQUFHLENBQUMsQ0FBQztBQUN4QyxHQUFHLENBQUM7QUFDSixDQUFDO0FBQ0Q7QUFDZSx1QkFBUSxDQUFDLEtBQUssRUFBRTtBQUMvQixFQUFFLE9BQU8sU0FBUyxDQUFDLE1BQU07QUFDekIsUUFBUSxJQUFJLENBQUMsSUFBSSxDQUFDLEtBQUssSUFBSSxJQUFJO0FBQy9CLFlBQVksVUFBVSxHQUFHLENBQUMsT0FBTyxLQUFLLEtBQUssVUFBVTtBQUNyRCxZQUFZLFlBQVk7QUFDeEIsWUFBWSxZQUFZLEVBQUUsS0FBSyxDQUFDLENBQUM7QUFDakMsUUFBUSxJQUFJLENBQUMsSUFBSSxFQUFFLENBQUMsU0FBUyxDQUFDO0FBQzlCOztBQ3hCQSxTQUFTLEtBQUssR0FBRztBQUNqQixFQUFFLElBQUksSUFBSSxDQUFDLFdBQVcsRUFBRSxJQUFJLENBQUMsVUFBVSxDQUFDLFdBQVcsQ0FBQyxJQUFJLENBQUMsQ0FBQztBQUMxRCxDQUFDO0FBQ0Q7QUFDZSx3QkFBUSxHQUFHO0FBQzFCLEVBQUUsT0FBTyxJQUFJLENBQUMsSUFBSSxDQUFDLEtBQUssQ0FBQyxDQUFDO0FBQzFCOztBQ05BLFNBQVMsS0FBSyxHQUFHO0FBQ2pCLEVBQUUsSUFBSSxJQUFJLENBQUMsZUFBZSxFQUFFLElBQUksQ0FBQyxVQUFVLENBQUMsWUFBWSxDQUFDLElBQUksRUFBRSxJQUFJLENBQUMsVUFBVSxDQUFDLFVBQVUsQ0FBQyxDQUFDO0FBQzNGLENBQUM7QUFDRDtBQUNlLHdCQUFRLEdBQUc7QUFDMUIsRUFBRSxPQUFPLElBQUksQ0FBQyxJQUFJLENBQUMsS0FBSyxDQUFDLENBQUM7QUFDMUI7O0FDSmUseUJBQVEsQ0FBQyxJQUFJLEVBQUU7QUFDOUIsRUFBRSxJQUFJLE1BQU0sR0FBRyxPQUFPLElBQUksS0FBSyxVQUFVLEdBQUcsSUFBSSxHQUFHLE9BQU8sQ0FBQyxJQUFJLENBQUMsQ0FBQztBQUNqRSxFQUFFLE9BQU8sSUFBSSxDQUFDLE1BQU0sQ0FBQyxXQUFXO0FBQ2hDLElBQUksT0FBTyxJQUFJLENBQUMsV0FBVyxDQUFDLE1BQU0sQ0FBQyxLQUFLLENBQUMsSUFBSSxFQUFFLFNBQVMsQ0FBQyxDQUFDLENBQUM7QUFDM0QsR0FBRyxDQUFDLENBQUM7QUFDTDs7QUNKQSxTQUFTLFlBQVksR0FBRztBQUN4QixFQUFFLE9BQU8sSUFBSSxDQUFDO0FBQ2QsQ0FBQztBQUNEO0FBQ2UseUJBQVEsQ0FBQyxJQUFJLEVBQUUsTUFBTSxFQUFFO0FBQ3RDLEVBQUUsSUFBSSxNQUFNLEdBQUcsT0FBTyxJQUFJLEtBQUssVUFBVSxHQUFHLElBQUksR0FBRyxPQUFPLENBQUMsSUFBSSxDQUFDO0FBQ2hFLE1BQU0sTUFBTSxHQUFHLE1BQU0sSUFBSSxJQUFJLEdBQUcsWUFBWSxHQUFHLE9BQU8sTUFBTSxLQUFLLFVBQVUsR0FBRyxNQUFNLEdBQUcsUUFBUSxDQUFDLE1BQU0sQ0FBQyxDQUFDO0FBQ3hHLEVBQUUsT0FBTyxJQUFJLENBQUMsTUFBTSxDQUFDLFdBQVc7QUFDaEMsSUFBSSxPQUFPLElBQUksQ0FBQyxZQUFZLENBQUMsTUFBTSxDQUFDLEtBQUssQ0FBQyxJQUFJLEVBQUUsU0FBUyxDQUFDLEVBQUUsTUFBTSxDQUFDLEtBQUssQ0FBQyxJQUFJLEVBQUUsU0FBUyxDQUFDLElBQUksSUFBSSxDQUFDLENBQUM7QUFDbkcsR0FBRyxDQUFDLENBQUM7QUFDTDs7QUNiQSxTQUFTLE1BQU0sR0FBRztBQUNsQixFQUFFLElBQUksTUFBTSxHQUFHLElBQUksQ0FBQyxVQUFVLENBQUM7QUFDL0IsRUFBRSxJQUFJLE1BQU0sRUFBRSxNQUFNLENBQUMsV0FBVyxDQUFDLElBQUksQ0FBQyxDQUFDO0FBQ3ZDLENBQUM7QUFDRDtBQUNlLHlCQUFRLEdBQUc7QUFDMUIsRUFBRSxPQUFPLElBQUksQ0FBQyxJQUFJLENBQUMsTUFBTSxDQUFDLENBQUM7QUFDM0I7O0FDUEEsU0FBUyxzQkFBc0IsR0FBRztBQUNsQyxFQUFFLElBQUksS0FBSyxHQUFHLElBQUksQ0FBQyxTQUFTLENBQUMsS0FBSyxDQUFDLEVBQUUsTUFBTSxHQUFHLElBQUksQ0FBQyxVQUFVLENBQUM7QUFDOUQsRUFBRSxPQUFPLE1BQU0sR0FBRyxNQUFNLENBQUMsWUFBWSxDQUFDLEtBQUssRUFBRSxJQUFJLENBQUMsV0FBVyxDQUFDLEdBQUcsS0FBSyxDQUFDO0FBQ3ZFLENBQUM7QUFDRDtBQUNBLFNBQVMsbUJBQW1CLEdBQUc7QUFDL0IsRUFBRSxJQUFJLEtBQUssR0FBRyxJQUFJLENBQUMsU0FBUyxDQUFDLElBQUksQ0FBQyxFQUFFLE1BQU0sR0FBRyxJQUFJLENBQUMsVUFBVSxDQUFDO0FBQzdELEVBQUUsT0FBTyxNQUFNLEdBQUcsTUFBTSxDQUFDLFlBQVksQ0FBQyxLQUFLLEVBQUUsSUFBSSxDQUFDLFdBQVcsQ0FBQyxHQUFHLEtBQUssQ0FBQztBQUN2RSxDQUFDO0FBQ0Q7QUFDZSx3QkFBUSxDQUFDLElBQUksRUFBRTtBQUM5QixFQUFFLE9BQU8sSUFBSSxDQUFDLE1BQU0sQ0FBQyxJQUFJLEdBQUcsbUJBQW1CLEdBQUcsc0JBQXNCLENBQUMsQ0FBQztBQUMxRTs7QUNaZSx3QkFBUSxDQUFDLEtBQUssRUFBRTtBQUMvQixFQUFFLE9BQU8sU0FBUyxDQUFDLE1BQU07QUFDekIsUUFBUSxJQUFJLENBQUMsUUFBUSxDQUFDLFVBQVUsRUFBRSxLQUFLLENBQUM7QUFDeEMsUUFBUSxJQUFJLENBQUMsSUFBSSxFQUFFLENBQUMsUUFBUSxDQUFDO0FBQzdCOztBQ0pBLFNBQVMsZUFBZSxDQUFDLFFBQVEsRUFBRTtBQUNuQyxFQUFFLE9BQU8sU0FBUyxLQUFLLEVBQUU7QUFDekIsSUFBSSxRQUFRLENBQUMsSUFBSSxDQUFDLElBQUksRUFBRSxLQUFLLEVBQUUsSUFBSSxDQUFDLFFBQVEsQ0FBQyxDQUFDO0FBQzlDLEdBQUcsQ0FBQztBQUNKLENBQUM7QUFDRDtBQUNBLFNBQVNFLGdCQUFjLENBQUMsU0FBUyxFQUFFO0FBQ25DLEVBQUUsT0FBTyxTQUFTLENBQUMsSUFBSSxFQUFFLENBQUMsS0FBSyxDQUFDLE9BQU8sQ0FBQyxDQUFDLEdBQUcsQ0FBQyxTQUFTLENBQUMsRUFBRTtBQUN6RCxJQUFJLElBQUksSUFBSSxHQUFHLEVBQUUsRUFBRSxDQUFDLEdBQUcsQ0FBQyxDQUFDLE9BQU8sQ0FBQyxHQUFHLENBQUMsQ0FBQztBQUN0QyxJQUFJLElBQUksQ0FBQyxJQUFJLENBQUMsRUFBRSxJQUFJLEdBQUcsQ0FBQyxDQUFDLEtBQUssQ0FBQyxDQUFDLEdBQUcsQ0FBQyxDQUFDLEVBQUUsQ0FBQyxHQUFHLENBQUMsQ0FBQyxLQUFLLENBQUMsQ0FBQyxFQUFFLENBQUMsQ0FBQyxDQUFDO0FBQ3pELElBQUksT0FBTyxDQUFDLElBQUksRUFBRSxDQUFDLEVBQUUsSUFBSSxFQUFFLElBQUksQ0FBQyxDQUFDO0FBQ2pDLEdBQUcsQ0FBQyxDQUFDO0FBQ0wsQ0FBQztBQUNEO0FBQ0EsU0FBUyxRQUFRLENBQUMsUUFBUSxFQUFFO0FBQzVCLEVBQUUsT0FBTyxXQUFXO0FBQ3BCLElBQUksSUFBSSxFQUFFLEdBQUcsSUFBSSxDQUFDLElBQUksQ0FBQztBQUN2QixJQUFJLElBQUksQ0FBQyxFQUFFLEVBQUUsT0FBTztBQUNwQixJQUFJLEtBQUssSUFBSSxDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUMsR0FBRyxDQUFDLENBQUMsRUFBRSxDQUFDLEdBQUcsRUFBRSxDQUFDLE1BQU0sRUFBRSxDQUFDLEVBQUUsQ0FBQyxHQUFHLENBQUMsRUFBRSxFQUFFLENBQUMsRUFBRTtBQUMxRCxNQUFNLElBQUksQ0FBQyxHQUFHLEVBQUUsQ0FBQyxDQUFDLENBQUMsRUFBRSxDQUFDLENBQUMsUUFBUSxDQUFDLElBQUksSUFBSSxDQUFDLENBQUMsSUFBSSxLQUFLLFFBQVEsQ0FBQyxJQUFJLEtBQUssQ0FBQyxDQUFDLElBQUksS0FBSyxRQUFRLENBQUMsSUFBSSxFQUFFO0FBQy9GLFFBQVEsSUFBSSxDQUFDLG1CQUFtQixDQUFDLENBQUMsQ0FBQyxJQUFJLEVBQUUsQ0FBQyxDQUFDLFFBQVEsRUFBRSxDQUFDLENBQUMsT0FBTyxDQUFDLENBQUM7QUFDaEUsT0FBTyxNQUFNO0FBQ2IsUUFBUSxFQUFFLENBQUMsRUFBRSxDQUFDLENBQUMsR0FBRyxDQUFDLENBQUM7QUFDcEIsT0FBTztBQUNQLEtBQUs7QUFDTCxJQUFJLElBQUksRUFBRSxDQUFDLEVBQUUsRUFBRSxDQUFDLE1BQU0sR0FBRyxDQUFDLENBQUM7QUFDM0IsU0FBUyxPQUFPLElBQUksQ0FBQyxJQUFJLENBQUM7QUFDMUIsR0FBRyxDQUFDO0FBQ0osQ0FBQztBQUNEO0FBQ0EsU0FBUyxLQUFLLENBQUMsUUFBUSxFQUFFLEtBQUssRUFBRSxPQUFPLEVBQUU7QUFDekMsRUFBRSxPQUFPLFdBQVc7QUFDcEIsSUFBSSxJQUFJLEVBQUUsR0FBRyxJQUFJLENBQUMsSUFBSSxFQUFFLENBQUMsRUFBRSxRQUFRLEdBQUcsZUFBZSxDQUFDLEtBQUssQ0FBQyxDQUFDO0FBQzdELElBQUksSUFBSSxFQUFFLEVBQUUsS0FBSyxJQUFJLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQyxHQUFHLEVBQUUsQ0FBQyxNQUFNLEVBQUUsQ0FBQyxHQUFHLENBQUMsRUFBRSxFQUFFLENBQUMsRUFBRTtBQUN2RCxNQUFNLElBQUksQ0FBQyxDQUFDLEdBQUcsRUFBRSxDQUFDLENBQUMsQ0FB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QUFDLEVBQUUsQ0FBQyxDQUFDLENBQUMsQ0FBQyxHQUFHQSxLQUFHLENBQUMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxFQUFFLFFBQVEsQ0FBQyxJQUFJLEVBQUUsSUFBSSxDQUFDLENBQUM7QUFDcEYsS0FBSztBQUNMO0FBQ0EsSUFBSSxPQUFPLElBQUksQ0FBQztBQUNoQixHQUFHO0FBQ0gsRUFBRSxJQUFJLEVBQUUsV0FBVztBQUNuQixJQUFJLElBQUksSUFBSSxHQUFHLEVBQUUsRUFBRSxDQUFDLEdBQUcsSUFBSSxDQUFDLENBQUMsQ0FBQztBQUM5QixJQUFJLEtBQUssSUFBSSxDQUFDLElBQUksQ0FBQyxFQUFFLElBQUksQ0FBQyxDQUFDLENBQUMsR0FBRyxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUMsS0FBSyxFQUFFLENBQUM7QUFDNUMsSUFBSSxPQUFPLElBQUksUUFBUSxDQUFDLElBQUksQ0FBQyxDQUFDO0FBQzlCLEdBQUc7QUFDSCxFQUFFLElBQUksRUFBRSxTQUFTLElBQUksRUFBRSxJQUFJLEVBQUU7QUFDN0IsSUFBSSxJQUFJLENBQUMsQ0FBQyxHQUFHLFNBQVMsQ0FBQyxNQUFNLEdBQUcsQ0FBQyxJQUFJLENBQUMsRUFBRSxLQUFLLElBQUksSUFBSSxHQUFHLElBQUksS0FBSyxDQUFDLENBQUMsQ0FBQyxFQUFFLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQyxFQUFFLENBQUMsRUFBRSxDQUFDLEdBQUcsQ0FBQyxFQUFFLEVBQUUsQ0FBQyxFQUFFLElBQUksQ0FBQyxDQUFDLENBQUMsR0FBRyxTQUFTLENBQUMsQ0FBQyxHQUFHLENBQUMsQ0FBQyxDQUFDO0FBQzFILElBQUksSUFBSSxDQUFDLElBQUksQ0FBQyxDQUFDLENBQUMsY0FBYyxDQUFDLElBQUksQ0FBQyxFQUFFLE1BQU0sSUFBSSxLQUFLLENBQUMsZ0JBQWdCLEdBQUcsSUFBSSxDQUFDLENBQUM7QUFDL0UsSUFBSSxLQUFLLENBQUMsR0FBRyxJQUFJLENBQUMsQ0FBQyxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUMsR0FBRyxDQUFD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RyxRQUFRLENBQUMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxFQUFFLEVBQUUsQ0FBQyxFQUFFLENBQUMsS0FBSyxDQUFDLEdBQUcsSUFBSSxDQUFDLENBQUMsQ0FBQztBQUMvRixRQUFRLENBQUMsS0FBSyxDQUFDLEdBQUcsSUFBSSxHQUFHLENBQUMsQ0FBQyxDQUFDLElBQUksQ0FBQyxHQUFHLEdBQUcsS0FBSyxDQUFDLElBQUksQ0FBQyxHQUFHLElBQUksQ0FBQyxFQUFFLENBQUMsQ0FBQyxJQUFJLENBQUMsR0FBRyxHQUFHLEtBQUssQ0FBQyxHQUFHLElBQUksQ0FBQyxFQUFFLENBQUMsQ0FBQyxDQUFDLEdBQUcsR0FBRyxLQUFLLENBQUMsS0FBSyxDQUFDLEdBQUcsR0FBRyxDQUFDLEVBQUUsQ0FBQyxDQUFDO0FBQ3pILFFBQVEsQ0FBQyxLQUFLLENBQUMsR0FBRyxJQUFJLENBQUMsQ0FBQyxJQUFJLEVBQUUsR0FBRyxJQUFJLEVBQUUsQ0FBQyxJQUFJLEVBQUUsR0FBRyxJQUFJLEVBQUUsQ0FBQyxJQUFJLENBQUMsR0FBRyxJQUFJLEVBQUUsQ0FBQyxDQUFDLEdBQUcsSUFBSSxJQUFJLElBQUksQ0FBQztBQUN4RixRQUFRLENBQUMsS0FBSyxDQUFDLEdBQUcsSUFBSSxDQUFDLENBQUMsQ0FBQyxJQUFJLEVBQUUsR0FBRyxHQUFHLEtBQUssQ0FBQyxJQUFJLENBQUMsR0FBRyxJQUFJLENBQUMsRUFBRSxDQUFDLENBQUMsSUFBSSxDQUFDLEdBQUcsR0FBRyxLQUFLLENBQUMsSUFBSSxDQUFDLEdBQUcsSUFBSSxDQUFDLEVBQUUsQ0FBQyxDQUFDLElBQUksQ0FBQyxHQUFHLEdBQUcsS0FBSyxDQUFDLEdBQUcsSUFBSSxDQUFDLEVBQUUsQ0FBQyxDQUFDLENBQUMsQ0FBQyxHQUFHLEdBQUcsS0FBSyxDQUFDLEtBQUssQ0FBQyxHQUFHLEdBQUcsQ0FBQyxJQUFJLElBQUksQ0FBQztBQUMvSixRQUFRLElBQUk7QUFDWixRQUFRLENBQUMsQ0FBQyxHQUFHLFlBQVksQ0FBQyxJQUFJLENBQUMsTUFBTSxDQUFDLElBQUksSUFBSSxHQUFHLENBQUMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxFQUFFLENBQUMsQ0FBQyxDQUFDLENBQUMsRUFBRSxDQUFDLENBQUMsQ0FBQyxDQUFDLEVBQUUsQ0FBQyxDQUFDO0FBQ3RFLFFBQVEsQ0FBQyxDQUFDLEdBQUcsWUFBWSxDQUFDLElBQUksQ0FBQyxNQUFNLENBQUMsSUFBSSxJQUFJLEdBQUcsQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDLEdBQUcsR0FBRyxHQUFHLEdBQUcsRUFBRSxDQUFDLENBQUMsQ0FBQyxDQUFDLEdBQUcsR0FBRyxHQUFHLEdBQUcsRUFBRSxDQUFDLENBQUMsQ0FBQyxDQUFDLEdBQUcsR0FBRyxHQUFHLEdBQUcsRUFBRSxDQUFDLENBQUM7QUFDMUcsUUFBUSxDQUFDLENBQUMsR0FBRyxhQUFhLENBQUMsSUFBSSxDQUFDLE1BQU0sQ0FBQyxJQUFJLElBQUksQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDLEVBQUUsQ0FBQyxDQUFDLENBQUMsQ0FBQyxFQUFFLENBQUMsQ0FBQyxDQUFDLENBQUMsRUFBRSxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUM7QUFDdkUsUUFBUSxDQUFDLENBQUMsR0FBRyxhQUFhLENBQUMsSUFBSSxDQUFDLE1BQU0sQ0FBQyxJQUFJLElBQUksQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDLEdBQUcsR0FBRyxHQUFHLEdBQUcsRUFBRSxDQUFDLENBQUMsQ0FBQyxDQUFDLEdBQUcsR0FBRyxHQUFHLEdBQUcsRUFBRSxDQUFDLENBQUMsQ0FBQyxDQUFDLEdBQUcsR0FBRyxHQUFHLEdBQUcsRUFBRSxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUM7QUFDM0csUUFBUSxDQUFDLENBQUMsR0FBRyxZQUFZLENBQUMsSUFBSSxDQUFDLE1BQU0sQ0FBQyxJQUFJLElBQUksQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDLEVBQUUsQ0FBQyxDQUFDLENBQUMsQ0FBQyxHQUFHLEdBQUcsRUFBRSxDQUFDLENBQUMsQ0FBQyxDQUFDLEdBQUcsR0FBRyxFQUFFLENBQUMsQ0FBQztBQUMvRSxRQUFRLENBQUMsQ0FBQyxHQUFHLGFBQWEsQ0FBQyxJQUFJLENBQUMsTUFBTSxDQUFDLElBQUksSUFBSSxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUMsRUFBRSxDQUFDLENBQUMsQ0FBQyxDQUFDLEdBQUcsR0FBRyxFQUFFLENBQUMsQ0FBQyxDQUFDLENBQUMsR0FBRyxHQUFHLEVBQUUsQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDO0FBQ25GLFFBQVEsS0FBSyxDQUFDLGNBQWMsQ0FBQyxNQUFNLENBQUMsR0FBRyxJQUFJLENBQUMsS0FBSyxDQUFDLE1BQU0sQ0FBQyxDQUFDO0FBQzFELFFBQVEsTUFBTSxLQUFLLGFBQWEsR0FBRyxJQUFJLEdBQUcsQ0FBQyxHQUFHLEVBQUUsR0FBRyxFQUFFLEdBQUcsRUFBRSxDQUFDLENBQUM7QUFDNUQsUUFBUSxJQUFJLENBQUM7QUFDYixDQUFDO0FBQ0Q7QUFDQSxTQUFTLElBQUksQ0FBQyxDQUFDLEVBQUU7QUFDakIsRUFBRSxPQUFPLElBQUksR0FBRyxDQUFDLENBQUMsSUFBSSxFQUFFLEdBQUcsSUFBSSxFQUFFLENBQUMsSUFBSSxDQUFDLEdBQUcsSUFBSSxFQUFFLENBQUMsR0FBRyxJQUFJLEVBQUUsQ0FBQyxDQUFDLENBQUM7QUFDN0QsQ0FBQztBQUNEO0FBQ0EsU0FBUyxJQUFJLENBQUMsQ0FBQyxFQUFFLENBQUMsRUFBRSxDQUFDLEVBQUUsQ0FBQyxFQUFFO0FBQzFCLEVBQUUsSUFBSSxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUMsR0FBRyxDQUFDLEdBQUcsQ0FBQyxHQUFHLEdBQUcsQ0FBQztBQUM5QixFQUFFLE9BQU8sSUFBSSxHQUFHLENBQUMsQ0FBQyxFQUFFLENBQUMsRUFBRSxDQUFDLEVBQUUsQ0FBQyxDQUFDLENBQUM7QUFDN0IsQ0FBQztBQUNEO0FBQ08sU0FBUyxVQUFVLENBQUMsQ0FBQyxFQUFFO0FBQzlCLEVBQUUsSUFBSSxFQUFFLENBQUMsWUFBWSxLQUFLLENBQUMsRUFBRSxDQUFDLEdBQUcsS0FBSyxDQUFDLENBQUMsQ0FBQyxDQUFDO0FBQzFDLEVBQUUsSUFBSSxDQUFDLENBQUMsRUFBRSxPQUFPLElBQUksR0FBRyxDQUFDO0FBQ3pCLEVBQUUsQ0FBQyxHQUFHLENBQUMsQ0FBQyxHQUFHLEVBQUUsQ0FBQztBQUNkLEVBQUUsT0FBTyxJQUFJLEdBQUcsQ0FBQyxDQUFDLENBQUMsQ0FBQyxFQUFFLENBQUMsQ0FBQyxDQUFDLEVBQUUsQ0FBQyxDQUFDLENBQUMsRUFBRSxDQUFDLENBQUMsT0FBTyxDQUFDLENBQUM7QUFDM0MsQ0FBQztBQUNEO0FBQ08sU0FBUyxHQUFHLENBQUMsQ0FBQyxFQUFFLENBQUMsRUFBRSxDQUFDLEVBQUUsT0FBTyxFQUFFO0FBQ3RDLEVBQUUsT0FBTyxTQUFTLENBQUMsTUFBTSxLQUFLLENBQUMsR0FBRyxVQUFVLENBQUMsQ0FBQyxDQUFDLEdBQUcsSUFBSSxHQUFHLENBQUMsQ0FBQyxFQUFFLENBQUMsRUFBRSxDQUFDLEVBQUUsT0FBTyxJQUFJLElBQUksR0FBRyxDQUFDLEdBQUcsT0FBTyxDQUFDLENBQUM7QUFDbEcsQ0FBQztBQUNEO0FBQ08sU0FBUyxHQUFHLENBQUMsQ0FBQyxFQUFFLENBQUMsRUFBRSxDQUFDLEVBQUUsT0FBTyxFQUFFO0FBQ3RDLEVBQUUsSUFBSSxDQUFDLENBQUMsR0FBRyxDQUFDLENBQUMsQ0FBQztBQUNkLEVBQUUsSUFBSSxDQUFDLENBQUMsR0FBRyxDQUFDLENBQUMsQ0FBQztBQUNkLEVBQUUsSUFBSSxDQUFDLENBQUMsR0FBRyxDQUFDLENBQUMsQ0FBQztBQUNkLEVBQUUsSUFBSSxDQUFDLE9BQU8sR0FBRyxDQUFDLE9BQU8sQ0FBQztBQUMxQixDQUFDO0FBQ0Q7QUFDQSxNQUFNLENBQUMsR0FBRyxFQUFFLEdBQUcsRUFBRSxNQUFNLENBQUMsS0FBSyxFQUFFO0FBQy9CLEVBQUUsUUFBUSxDQUFDLENBQUMsRUFBRTtBQUNkLElBQUksQ0FBQyxHQUFHLENBQUMsSUFBSSxJQUFJLEdBQUcsUUFBUSxHQUFHLElBQUksQ0FBQyxHQUFHLENBQUMsUUFBUSxFQUFFLENB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RUFBRSxDQUFDLEtBQUssQ0FBQyxHQUFHLE1BQU0sR0FBRyxPQUFPLENBQUMsRUFBRSxNQUFNLENBQUMsSUFBSSxDQUFDLENBQUMsQ0FBQyxDQUFDLEVBQUUsRUFBRSxNQUFNLENBQUMsSUFBSSxDQUFDLENBQUMsQ0FBQyxDQUFDLEVBQUUsRUFBRSxNQUFNLENBQUMsSUFBSSxDQUFDLENBQUMsQ0FBQyxDQUFDLEVBQUUsQ0FBQyxLQUFLLENBQUMsR0FBRyxHQUFHLEdBQUcsQ0FBQyxFQUFFLEVBQUUsQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUMsQ0FBQztBQUM1SCxDQUFDO0FBQ0Q7QUFDQSxTQUFTLE1BQU0sQ0FBQyxPQUFPLEVBQUU7QUFDekIsRUFBRSxPQUFPLEtBQUssQ0FBQyxPQUFPLENBQUMsR0FBRyxDQUFDLEdBQUcsSUFBSSxDQUFDLEdBQUcsQ0FBQyxDQUFDLEVBQUUsSUFBSSxDQUFDLEdBQUcsQ0FBQyxDQUFDLEVBQUUsT0FBTyxDQUFDLENBQUMsQ0FBQztBQUNoRSxDQUFDO0FBQ0Q7QUFDQSxTQUFTLE1BQU0sQ0FBQyxLQUFLLEVBQUU7QUFDdkIsRUFBRSxPQUFPLElBQUksQ0FBQyxHQUFHLENBQUMsQ0FBQyxFQUFFLElBQUksQ0FBQyxHQUFHLENBQUMsR0FBRyxFQUFFLElBQUksQ0FBQyxLQUFLLENBQUMsS0FBSyxDQUFDLElBQUksQ0FBQyxDQUFDLENBQUMsQ0FBQztBQUM1RCxDQUFDO0FBQ0Q7QUFDQSxTQUFTLEdBQUcsQ0FBQyxLQUFLLEVBQUU7QUFDcEIsRUFBRSxLQUFLLEdBQUcsTUFBTSxDQUFDLEtBQUssQ0FBQyxDQUFDO0FBQ3hCLEVBQUUsT0FBTyxDQUFDLEtBQUssR0FBRyxFQUFFLEdBQUcsR0FBRyxHQUFHLEVBQUUsSUFBSSxLQUFLLENBQUMsUUFBUSxDQUFDLEVBQUUsQ0FBQyxDQUFDO0FBQ3RELENBQUM7QUFDRDtBQUNBLFNBQVMsSUFBSSxDQUFDLENBQUMsRUFBRSxDQUFDLEVBQUUsQ0FBQyxFQUFFLENBQUMsRUFBRTtBQUMxQixFQUFFLElBQUksQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDLEdBQUcsQ0FBQyxHQUFHLENBQUMsR0FBRyxHQUFHLENBQUM7QUFDOUIsT0FBTyxJQUFJLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDLEdBQUcsQ0FBQyxHQUFHLEdBQUcsQ0FBQztBQUN6QyxPQUFPLElBQUksQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDLEdBQUcsR0FBRyxDQUFDO0FBQzNCLEVBQUUsT0FBTyxJQUFJLEdBQUcsQ0FBQyxDQUFDLEVBQUUsQ0FBQyxFQUFFLENBQUMsRUFBRSxDQUFDLENBQUMsQ0FBQztBQUM3QixDQUFDO0FBQ0Q7QUFDTyxTQUFTLFVBQVUsQ0FBQyxDQUFDLEVBQUU7QUFDOUIsRUFBRSxJQUFJLENBQUMsWUFBWSxHQUFHLEVBQUUsT0FBTyxJQUFJLEdBQUcsQ0FBQyxDQUFDLENBQUMsQ0FBQyxFQUFFLENBQUMsQ0FBQyxDQUFDLEVBQUUsQ0FBQyxDQUFDLENBQUMsRUFBRSxDQUFDLENBQUMsT0FBTyxDQUFDLENBQUM7QUFDakUsRUFBRSxJQUFJLEVBQUUsQ0FBQyxZQUFZLEtBQUssQ0FBQyxFQUFFLENBQUMsR0FBRyxLQUFLLENBQUMsQ0FBQyxDQUFDLENBQUM7QUFDMUMsRUFBRSxJQUFJLENBQUMsQ0FBQyxFQUFFLE9BQU8sSUFBSSxHQUFHLENBQUM7QUFDekIsRUFBRSxJQUFJLENBQUMsWUFBWSxHQUFHLEVBQUUsT0FBTyxDQUFDLENBQUM7QUFDakMsRUFBRSxDQUFDLEdBQUcsQ0FBQyxDQUFDLEdBQUcsRUFBRSxDQUFDO0FBQ2QsRUFBRSxJQUFJLENBQUMsR0FBRyxDQUFDLENBQUMsQ0FBQyxHQUFHLEdBQUc7QUFDbkIsTUFBTSxDQUFDLEdBQUcsQ0FBQyxDQUFDLENBQUMsR0FBRyxHQUFHO0FBQ25CLE1BQU0sQ0FBQyxHQUFHLENBQUMsQ0FBQyxDQUFDLEdBQUcsR0FBRztBQUNuQixNQUFNLEdBQUcsR0FBRyxJQUFJLENBQUMsR0FBRyxDQUFDLENBQUMsRUFBRSxDQUFDLEVBQUUsQ0FBQyxDQUFDO0FBQzdCLE1BQU0sR0FBRyxHQUFHLElBQUksQ0FBQyxHQUFHLENBQUMsQ0FBQyxFQUFFLENBQUMsRUFBRSxDQUFDLENBQUM7QUFDN0IsTUFBTSxDQUFDLEdBQUcsR0FBRztBQUNiLE1BQU0sQ0FBQyxHQUFHLEdBQUcsR0FBRyxHQUFHO0FBQ25CLE1BQU0sQ0FBQyxHQUFHLENBQUMsR0FBRyxHQUFHLEdBQUcsSUFBSSxDQUFDLENBQUM7QUFDMUIsRUFBRSxJQUFJLENBQUMsRUFBRTtBQUNULElBQUksSUFBSSxDQUFDLEtBQUssR0FBRyxFQUFFLENBQUMsR0FBRyxDQUFDLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxHQUFHLENBQUMsQ0FBQyxHQUFHLENBQUMsSUFBSSxDQUFDLENBQUM7QUFDakQsU0FBUyxJQUFJLENBQUMsS0FBSyxHQUFHLEVBQUUsQ0FBQyxHQUFHLENBQUMsQ0FBQyxHQUFHLENBQUMsSUFBSSxDQUFDLEdBQUcsQ0FBQyxDQUFDO0FBQzVDLFNBQVMsQ0FBQyxHQUFHLENBQUMsQ0FBQyxHQUFHLENBQUMsSUFBSSxDQUFDLEdBQUcsQ0FBQyxDQUFDO0FBQzdCLElBQUksQ0FBQyxJQUFJLENBQUMsR0FBRyxHQUFHLEdBQUcsR0FBRyxHQUFHLEdBQUcsR0FBRyxDQUFDLEdBQUcsR0FBRyxHQUFHLEdBQUcsQ0FBQztBQUM3QyxJQUFJLENBQUMsSUFBSSxFQUFFLENBQUM7QUFDWixHQUFHLE1BQU07QUFDVCxJQUFJLENBQUMsR0FBRyxDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsR0FBRyxDQUFDLEdBQUcsQ0FBQyxHQUFHLENBQUMsQ0FBQztBQUMvQixHQUFHO0FBQ0gsRUFBRSxPQUFPLElBQUksR0FBRyxDQUFDLENBQUMsRUFBRSxDQUFDLEVBQUUsQ0FBQyxFQUFFLENBQUMsQ0FBQyxPQUFPLENBQUMsQ0FBQztBQUNyQyxDQUFDO0FBQ0Q7QUFDTyxTQUFTLEdBQUcsQ0FBQyxDQUFDLEVBQUUsQ0FBQyxFQUFFLENBQUMsRUFBRSxPQUFPLEVBQUU7QUFDdEMsRUFBRSxPQUFPLFNBQVMsQ0FBQyxNQUFNLEtBQUssQ0FBQyxHQUFHLFVBQVUsQ0FBQyxDQUFDLENBQUMsR0FBRyxJQUFJLEdBQUcsQ0FBQyxDQUFDLEVBQUUsQ0FBQyxFQUFFLENBQUMsRUFBRSxPQUFPLElBQUksSUFBSSxHQUFHLENBQUMsR0FBRyxPQUFPLENBQUMsQ0FBQztBQUNsRyxDQUFDO0FBQ0Q7QUFDQSxTQUFTLEdBQUcsQ0FBQyxDQUFDLEVBQUUsQ0FBQyxFQUFFLENBQUMsRUFBRSxPQUFPLEVBQUU7QUFDL0IsRUFBRSxJQUFJLENBQUMsQ0FBQyxHQUFHLENBQUMsQ0FBQyxDQUFDO0FBQ2QsRUFBRSxJQUFJLENBQUMsQ0FBQyxHQUFHLENBQUMsQ0FBQyxDQUFDO0FBQ2QsRUFBRSxJQUFJLENBQUMsQ0FBQyxHQUFHLENBQUMsQ0FBQyxDQUFDO0FBQ2QsRUFBRSxJQUFJLENBQUMsT0FBTyxHQUFHLENBQUMsT0FBTyxDQUFDO0FBQzFCLENBQUM7QUFDRDtBQUNBLE1BQU0sQ0FBQyxHQUFHLEVBQUUsR0FBRyxFQUFFLE1BQU0sQ0FBQyxLQUFLLEVBQUU7QUFDL0IsRUFBRSxRQUFRLENBQUMsQ0FBQyxFQUFFO0FBQ2QsSUFBSSxDQUFDLEdBQUcsQ0FBQyxJQUFJLElBQUksR0FBRyxRQUFRLEdBQUcsSUFBSSxDQUFDLEdBQUcsQ0FBQyxRQUFRLEVBQUUsQ0FBQyxDQUFDLENBQUM7QUFDckQsSUFBSSxPQUFPLElBQUksR0FBRyxDQUFDLElBQUksQ0FBQyxDQUFDLEVBQUUsSUFBSSxDQUFDLENBQUMsRUFBRSxJQUFJLENBQUMsQ0FBQyxHQUFHLENBQUMsRUFBRSxJQUFJLENBQUMsT0FBTyxDQUFDLENBQUM7QUFDN0QsR0FBRztBQUNILEVBQUUsTUFBTSxDQUFDLENBQUMsRUFBRTtBQUNaLElBQUksQ0FBQyxHQUFHLENBQUMsSUFBSSxJQUFJLEdBQUcsTUFBTSxHQUFHLElBQUksQ0FBQyxHQUFHLENBQUMsTUFBTSxFQUFFLENBQUMsQ0FBQyxDQUFDO0FBQ2pELElBQUksT0FBTyxJQUFJLEdBQUcsQ0FBQyxJQUFJLENBQUMsQ0FBQyxF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R0FBRyxHQUFHLEVBQUUsQ0FBQyxJQUFJLEdBQUcsQ0FBQztBQUNoRSxNQUFNLENBQUMsQ0FBQyxJQUFJLENBQUMsQ0FBQyxDQUFDLEVBQUUsQ0FBQyxDQUFDLElBQUksQ0FBQyxHQUFHLENBQUMsQ0FBQyxDQUFDLEdBQUcsU0FBUyxFQUFFLElBQUksRUFBRSxRQUFRLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQyxFQUFFQSxpQkFBTSxDQUFDLENBQUMsRUFBRSxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUM7QUFDbkYsS0FBSyxNQUFNLElBQUksQ0FBQyxFQUFFO0FBQ2xCLE1BQU0sQ0FBQyxDQUFDLElBQUksQ0FBQyxHQUFHLENBQUMsQ0FBQyxDQUFDLEdBQUcsU0FBUyxHQUFHLENBQUMsR0FBRyxRQUFRLENBQUMsQ0FBQztBQUNoRCxLQUFLO0FBQ0wsR0FBRztBQUNIO0FBQ0EsRUFBRSxTQUFTLEtBQUssQ0FBQyxDQUFDLEVBQUUsQ0FBQyxFQUFFLENBQUMsRUFBRSxDQUFDLEVBQUU7QUFDN0IsSUFBSSxJQUFJLENBQUMsS0FBSyxDQUFDLEVBQUU7QUFDakIsTUFBTSxDQUFDLENBQUMsSUFBSSxDQUFDLENBQUMsQ0FBQyxFQUFFLENBQUMsQ0FBQyxJQUFJLENBQUMsR0FBRyxDQUFDLENBQUMsQ0FBQyxHQUFHLFFBQVEsRUFBRSxJQUFJLEVBQUUsUUFBUSxDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUMsRUFBRUEsaUJBQU0sQ0FBQyxDQUFDLEVBQUUsQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDO0FBQ2xGLEtBQUssTUFBTSxJQUFJLENBQUMsRUFBRTtBQUNsQixNQUFNLENBQUMsQ0FBQyxJQUFJLENBQUMsR0FBRyxDQUFDLENBQUMsQ0FBQyxHQUFHLFFBQVEsR0FBRyxDQUFDLEdBQUcsUUFBUSxDQUFDLENBQUM7QUFDL0MsS0FBSztBQUNMLEdBQUc7QUFDSDtBQUNBLEVBQUUsU0FBUyxLQUFLLENBQUMsRUFBRSxFQUFFLEVBQUUsRUFBRSxFQUFFLEVBQUUsRUFBRSxFQUFFLENBQUMsRUFBRSxDQUFDLEVBQUU7QUFDdkMsSUFBSSxJQUFJLEVBQUUsS0FBSyxFQUFFLElBQUksRUFBRSxLQUFLLEVBQUUsRUFBRTtBQUNoQyxNQUFNLElBQUksQ0FBQyxHQUFHLENBQUMsQ0FBQyxJQUFJLENBQUMsR0FBRyxDQUFDLENBQUMsQ0FBQyxHQUFHLFFBQVEsRUFBRSxJQUFJLEVBQUUsR0FBRyxFQUFFLElBQUksRUFBRSxHQUFHLENBQUMsQ0FBQztBQUM5RCxNQUFNLENBQUMsQ0FBQyxJQUFJLENBQUMsQ0FBQyxDQUFDLEVBQUUsQ0FBQyxHQUFHLENBQUMsRUFBRSxDQUFDLEVBQUVBLGlCQUFNLENBQUMsRUFBRSxFQUFFLEVBQUUsQ0FBQyxDQUFDLEVBQUUsQ0FBQyxDQUFDLEVBQUUsQ0FBQyxHQUFHLENBQUMsRUFBRSxDQUFDLEVBQUVBLGlCQUFNLENBQUMsRUFBRSxFQUFFLEVBQUUsQ0FBQyxDQUFDLENBQUMsQ0FBQztBQUMzRSxLQUFLLE1BQU0sSUFBSSxFQUFFLEtBQUssQ0FBQyxJQUFJLEVBQUUsS0FBSyxDQUFDLEVBQUU7QUFDckMsTUFBTSxDQUFDLENBQUMsSUFBSSxDQUFDLEdBQUcsQ0FBQyxDQUFDLENBQUMsR0FBRyxRQUFRLEdBQUcsRUFBRSxHQUFHLEdBQUcsR0FBRyxFQUFFLEdBQUcsR0FBRyxDQUFDLENBQUM7QUFDdEQsS0FBSztBQUNMLEdBQUc7QUFDSDtBQUNBLEVBQUUsT0FBTyxTQUFTLENBQUMsRUFBRSxDQUFDLEVBQUU7QUFDeEIsSUFBSSxJQUFJLENBQUMsR0FBRyxFQUFFO0FBQ2QsUUFBUSxDQUFDLEdBQUcsRUFBRSxDQUFDO0FBQ2YsSUFBSSxDQUFDLEdBQUcsS0FBSyxDQUFDLENBQUMsQ0FBQyxFQUFFLENBQUMsR0FBRyxLQUFLLENBQUMsQ0FBQyxDQUFDLENBQUM7QUFDL0IsSUFBSSxTQUFTLENBQUMsQ0FBQyxDQUFDLFVBQVUsRUFBRSxDQUFDLENBQUMsVUFBVSxFQUFFLENBQUMsQ0FBQyxVQUFVLEVBQUUsQ0FBQyxDQUFDLFVBQVUsRUFBRSxDQUFDLEVBQUUsQ0FBQyxDQUFDLENBQUM7QUFDNUUsSUFBSSxNQUFNLENBQUMsQ0FBQyxDQUFDLE1BQU0sRUFBRSxDQUFDLENBQUMsTUFBTSxFQUFFLENBQUMsRUFBRSxDQUFDLENBQUMsQ0FBQztBQUNyQyxJQUFJLEtBQUssQ0FBQyxDQUFDLENBQUMsS0FBSyxFQUFFLENBQUMsQ0FBQyxLQUFLLEVBQUUsQ0FBQyxFQUFFLENBQUMsQ0FBQyxDQUFDO0FBQ2xDLElBQUksS0FBSyxDQUFDLENBQUMsQ0FBQyxNQUFNLEVBQUUsQ0FBQyxDQUFDLE1BQU0sRUFBRSxDQUFDLENBQUMsTUFBTSxFQUFFLENBQUMsQ0FBQyxNQUFNLEVBQUUsQ0FBQyxFQUFFLENBQUMsQ0FBQyxDQUFDO0FBQ3hELElBQUksQ0FBQyxHQUFHLENBQUMsR0FBRyxJQUFJLENBQUM7QUFDakIsSUFBSSxPQUFPLFNBQVMsQ0FBQyxFQUFFO0FBQ3ZCLE1BQU0sSUFBSSxDQUFDLEdBQUcsQ0FBQyxDQUFDLEVBQUUsQ0FBQyxHQUFHLENBQUMsQ0FBQyxNQUFNLEVBQUUsQ0FBQyxDQUFDO0FBQ2xDLE1BQU0sT0FBTyxFQUFFLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQyxDQUFDLENBQUMsQ0FBQyxHQUFHLENBQUMsQ0FBQyxDQUFDLENBQUMsRUFBRSxDQUFDLENBQUMsR0FBRyxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDO0FBQy9DLE1BQU0sT0FBTyxDQUFDLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQyxDQUFDO0FBQ3hCLEtBQUssQ0FBQztBQUNOLEdBQUcsQ0FBQztBQUNKLENBQUM7QUFDRDtBQUNPLElBQUksdUJBQXVCLEdBQUcsb0JBQW9CLENBQUMsUUFBUSxFQUFFLE1BQU0sRUFBRSxLQUFLLEVBQUUsTUFBTSxDQUFDLENBQUM7QUFDcEYsSUFBSSx1QkFBdUIsR0FBRyxvQkFBb0IsQ0FBQyxRQUFRLEVBQUUsSUFBSSxFQUFFLEdBQUcsRUFBRSxHQUFHLENBQUM7O0FDOURuRixJQUFJLFFBQVEsR0FBRyxLQUFLLENBQUM7QUFDckI7QUFDQSxTQUFTLElBQUksQ0FBQyxDQUFDLEVBQUU7QUFDakIsRUFBRSxPQUFPLENBQUMsQ0FBQyxDQUFDLEdBQUcsSUFBSSxDQUFDLEdBQUcsQ0FBQyxDQUFDLENBQUMsSUFBSSxDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsQ0FBQztBQUN6QyxDQUFDO0FBQ0Q7QUFDQSxTQUFTLElBQUksQ0FBQyxDQUFDLEVBQUU7QUFDakIsRUFBRSxPQUFPLENBQUMsQ0FBQyxDQUFDLEdBQUcsSUFBSSxDQUFDLEdBQUcsQ0FBQyxDQUFDLENBQUMsSUFBSSxDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsQ0FBQztBQUN6QyxDQUFDO0FBQ0Q7QUFDQSxTQUFTLElBQUksQ0FBQyxDQUFDLEVBQUU7QUFDakIsRUFBRSxPQUFPLENBQUMsQ0FBQyxDQUFDLEdBQUcsSUFBSSxDQUFDLEdBQUcsQ0FBQyxDQUFDLEdBQUcsQ0FBQyxDQUFDLElBQUksQ0FBQyxLQUFLLENBQUMsR0FBRyxDQUFDLENBQUMsQ0FBQztBQUMvQyxDQUFDO0FBQ0Q7QUFDQSxzQkFBZSxDQUFDLFNBQVMsT0FBTyxDQUFDLEdBQUcsRUFBRSxJQUFJLEVBQUUsSUFBSSxFQUFFO0FBQ2xEO0FBQ0E7QUFDQTtBQUNBLEVBQUUsU0FBUyxJQUFJLENBQUMsRUFBRSxFQUFFLEVBQUUsRUFBRTtBQUN4QixJQUFJLElBQUksR0FBRyxHQUFHLEVBQUUsQ0FBQyxDQUFDLENBQUMsRUFBRSxHQUFHLEdBQUcsRUFBRSxDQUFDLENBQUMsQ0FBQyxFQUFFLEVBQUUsR0FBRyxFQUFFLENBQUMsQ0FBQyxDQUFDO0FBQzVDLFFBQVEsR0FBRyxHQUFHLEVBQUUsQ0FBQyxDQUFDLENBQUMsRUFBRSxHQUFHLEdBQUcsRUFBRSxDQUFDLENBQUMsQ0FBQyxFQUFFLEVBQUUsR0FBRyxFQUFFLENBQUMsQ0FBQyxDQUFDO0FBQzVDLFFBQVEsRUFBRSxHQUFHLEdBQUcsR0FBRyxHQUFHO0FBQ3RCLFFBQVEsRUFBRSxHQUFHLEdBQUcsR0FBRyxHQUFHO0FBQ3RCLFFBQVEsRUFBRSxHQUFHLEVBQUUsR0FBRyxFQUFFLEdBQUcsRUFBRSxHQUFHLEVBQUU7QUFDOUIsUUFBUSxDQUFDO0FBQ1QsUUFBUSxDQUFDLENBQUM7QUFDVjtBQUNBO0FBQ0EsSUFBSSxJQUFJLEVBQUUsR0FBRyxRQUFRLEVBQUU7QUFDdkIsTUFBTSxDQUFDLEdBQUcsSUFBSSxDQUFDLEdBQUcsQ0FBQyxFQUFFLEdBQUcsRUFBRSxDQUFDLEdBQUcsR0FBRyxDQUFDO0FBQ2xDLE1BQU0sQ0FBQyxHQUFHLFNBQVMsQ0FBQyxFQUFFO0FBQ3RCLFFBQVEsT0FBTztBQUNmLFVBQVUsR0FBRyxHQUFHLENBQUMsR0FBRyxFQUFFO0FBQ3RCLFVBQVUsR0FBRyxHQUFHLENBQUMsR0FBRyxFQUFFO0FBQ3RCLFVBQVUsRUFBRSxHQUFHLElBQUksQ0FBQyxHQUFHLENBQUMsR0FBRyxHQUFHLENBQUMsR0FBRyxDQUFDLENBQUM7QUFDcEMsU0FBUyxDQUFDO0FBQ1YsUUFBTztBQUNQLEtBQUs7QUFDTDtBQUNBO0FBQ0EsU0FBUztBQUNULE1BQU0sSUFBSSxFQUFFLEdBQUcsSUFBSSxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUM7QUFDNUIsVUFBVSxFQUFFLEdBQUcsQ0FBQyxFQUFFLEdBQUcsRUFBRSxHQUFHLEVBQUUsR0FBRyxFQUFFLEdBQUcsSUFBSSxHQUFHLEVBQUUsS0FBSyxDQUFDLEdBQUcsRUFBRSxHQUFHLElBQUksR0FBRyxFQUFFLENBQUM7QUFDckUsVUFBVSxFQUFFLEdBQUcsQ0FBQyxFQUFFLEdBQUcsRUFBRSxHQUFHLEVBQUUsR0FBRyxFQUFFLEdBQUcsSUFBSSxHQUFHLEVBQUUsS0FBSyxDQUFDLEdBQUcsRUFBRSxHQUFHLElBQUksR0FBRyxFQUFFLENBQUM7QUFDckUsVUFBVSxFQUFFLEdBQUcsSUFBSSxDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLEVBQUUsR0FBRyxFQUFFLEdBQUcsQ0FBQyxDQUFDLEdBQUcsRUFBRSxDQUFDO0FBQ3BELFVBQVUsRUFBRSxHQUFHLElBQUksQ0FBQyxHQUFHLENBQUMsSUFBSSxDQUFDLElBQUksQ0FBQyxFQUFFLEdBQUcsRUFBRSxHQUFHLENBQUMsQ0FBQyxHQUFHLEVBQUUsQ0FBQyxDQUFDO0FBQ3JELE1BQU0sQ0FBQyxHQUFHLENBQUMsRUFBRSxHQUFHLEVBQUUsSUFBSSxHQUFHLENBQUM7QUFDMUIsTUFBTSxDQUFDLEdBQUcsU0FBUyxDQUFDLEVBQUU7QUFDdEIsUUFBUSxJQUFJLENBQUMsR0FBRyxDQUFDLEdBQUcsQ0FBQztBQUNyQixZQUFZLE1BQU0sR0FBRyxJQUFJLENBQUMsRUFBRSxDQUFDO0FBQzdCLFlBQVksQ0FBQyxHQUFHLEVBQUUsSUFBSSxJQUFJLEdBQUcsRUFBRSxDQUFDLElBQUksTUFBTSxHQUFHLElBQUksQ0FBQyxHQUFHLEdBQUcsQ0FBQyxHQUFHLEVBQUUsQ0FBQyxHQUFHLElBQUksQ0FBQyxFQUFFLENBQUMsQ0FBQyxDQUFDO0FBQzVFLFFBQVEsT0FBTztBQUNmLFVBQVUsR0FBRyxHQUFHLENBQUMsR0FBRyxFQUFFO0FBQ3RCLFVBQVUsR0FBRyxHQUFHLENBQUMsR0FBRyxFQUFFO0FBQ3RCLFVBQVUsRUFBRSxHQUFHLE1BQU0sR0FBRyxJQUFJLENBQUMsR0FBRyxHQUFHLENBQUMsR0FBRyxFQUFFLENBQUM7QUFDMUMsU0FBUyxDQUFDO0FBQ1YsUUFBTztBQUNQLEtBQUs7QUFDTDtBQUNBLElBQUksQ0FBQyxDQUFDLFFBQVEsR0FBRyxDQUFDLEdBQUcsSUFBSSxHQUFHLEdBQUcsR0FBRyxJQUFJLENBQUMsS0FBSyxDQUFDO0FBQzdDO0FBQ0EsSUFBSSxPQUFPLENBQUMsQ0FBQztBQUNiLEdBQUc7QUFDSDtBQUNBLEVBQUUsSUFBSSxDQUFDLEdBQUcsR0FBRyxTQUFTLENBQUMsRUFBRTtBQUN6QixJQUFJLElBQUksRUFBRSxHQUFHLElBQUksQ0FBQyxHQUFHLENBQUMsSUFBSSxFQUFFLENBQUMsQ0FBQyxDQUFDLEVBQUUsRUFBRSxHQUFHLEVBQUUsR0FBRyxFQUFFLEVBQUUsRUFBRSxHQUFHLEVBQUUsR0FBRyxFQUFFLENBQUM7QUFDNUQsSUFBSSxPQUFPLE9BQU8sQ0FBQyxFQUFFLEVBQUUsRUFBRSxFQUFFLEVBQUUsQ0FBQyxDQUFDO0FBQy9CLEdBQUcsQ0FBQztBQUNKO0FBQ0EsRUFBRSxPQUFPLElBQUksQ0FBQztBQUNkLENBQUMsRUFBRSxJQUFJLENBQUMsS0FBSyxFQUFFLENBQUMsRUFBRSxDQUFDLENBQUM7O0FDdEVwQixJQUFJLEtBQUssR0FBRyxDQUFDO0FBQ2IsSUFBSUUsU0FBTyxHQUFHLENBQUM7QUFDZixJQUFJLFFBQVEsR0FBRyxDQUFDO0FBQ2hCLElBQUksU0FBUyxHQUFHLElBQUk7QUFDcEIsSUFBSSxRQUFRO0FBQ1osSUFBSSxRQUFRO0FBQ1osSUFBSSxTQUFTLEdBQUcsQ0FBQztBQUNqQixJQUFJLFFBQVEsR0FBRyxDQUFDO0FBQ2hCLElBQUksU0FBUyxHQUFHLENBQUM7QUFDakIsSUFBSSxLQUFLLEdBQUcsT0FBTyxXQUFXLEtBQUssUUFBUSxJQUFJLFdBQVcsQ0FBQyxHQUFHLEdBQUcsV0FBVyxHQUFHLElBQUk7QUFDbkYsSUFBSSxRQUFRLEdBQWlDLE1BQU0sQ0FBQyxxQkFBcUIsR0FBRyxNQUFNLENBQUMscUJBQXFCLENBQUMsSUFBSSxDQUFDLE1BQU0sQ0FBQyxHQUFHLFNBQVMsQ0FBQyxFQUFFLEVBQUUsVUFBVSxDQUFDLENBQUMsRUFBRSxFQUFFLENBQUMsQ0FBQyxFQUFFLENBQUM7QUFDM0o7QUFDTyxTQUFTLEdBQUcsR0FBRztBQUN0QixFQUFFLE9BQU8sUUFBUSxLQUFLLFFBQVEsQ0FBQyxRQUFRLENBQUMsRUFBRSxRQUFRLEdBQUcsS0FBSyxDQUFDLEdBQUcsRUFBRSxHQUFHLFNBQVMsQ0FBQyxDQUFDO0FBQzlFLENBQUM7QUFDRDtBQUNBLFNBQVMsUUFBUSxHQUFHO0FBQ3BCLEVBQUUsUUFBUSxHQUFHLENBQUMsQ0FBQztBQUNmLENBQUM7QUFDRDtBQUNPLFNBQVMsS0FBSyxHQUFHO0FBQ3hCLEVBQUUsSUFBSSxDQUFDLEtBQUs7QUFDWixFQUFFLElBQUksQ0FBQyxLQUFLO0FBQ1osRUFBRSxJQUFJLENBQUMsS0FBSyxHQUFHLElBQUksQ0FBQztBQUNwQixDQUFDO0FBQ0Q7QUFDQSxLQUFLLENBQUMsU0FBUyxHQUFHLEtBQUssQ0FBQyxTQUFTLEdBQUc7QUFDcEMsRUFBRSxXQUFXLEVBQUUsS0FBSztBQUNwQixFQUFFLE9BQU8sRUFBRSxTQUFTLFFBQVEsRUFBRSxLQUFLLEVBQUUsSUFBSSxFQUFFO0FBQzNDLElBQUksSUFBSSxPQUFPLFFBQVEsS0FBSyxVQUFVLEVBQUUsTUFBTSxJQUFJLFNBQVMsQ0FBQyw0QkFBNEIsQ0FBQyxDQUFDO0FBQzFGLElBQUksSUFBSSxHQUFHLENBQUMsSUFBSSxJQUFJLElBQUksR0FBRyxHQUFHLEVBQUUsR0FBRyxDQUFDLElBQUksS0FBSyxLQUFLLElBQUksSUFBSSxHQUFHLENBQUMsR0FBRyxDQUFDLEtBQUssQ0FBQyxDQUFDO0FBQ3pFLElBQUksSUFBSSxDQUFDLElBQUksQ0FBQyxLQUFLLElBQUksUUFBUSxLQUFLLElBQUksRUFBRTtBQUMxQyxNQUFNLElBQUksUUFBUSxFQUFFLFFBQVEsQ0FBQyxLQUFLLEdBQUcsSUFBSSxDQUFDO0FBQzFDLFdBQVcsUUFBUSxHQUFHLElBQUksQ0FBQztBQUMzQixNQUFNLFFBQVEsR0FBRyxJQUFJLENBQUM7QUFDdEIsS0FBSztBQUNMLElBQUksSUFBSSxDQUFDLEtBQUssR0FBRyxRQUFRLENBQUM7QUFDMUIsSUFBSSxJQUFJLENBQUMsS0FBSyxHQUFHLElBQUksQ0FBQztBQUN0QixJQUFJLEtBQUssRUFBRSxDQUFDO0FBQ1osR0FBRztBQUNILEVBQUUsSUFBSSxFQUFFLFdBQVc7QUFDbkIsSUFBSSxJQUFJLElBQUksQ0FBQyxLQUFLLEVBQUU7QUFDcEIsTUFBTSxJQUFJLENBQUMsS0FBSyxHQUFHLElBQUksQ0FBQztBQUN4QixNQUFNLElBQUksQ0FBQyxLQUFLLEdBQUcsUUFBUSxDQUFDO0FBQzVCLE1BQU0sS0FBSyxFQUFFLENBQUM7QUFDZCxLQUFLO0FBQ0wsR0FBRztBQUNILENBQUMsQ0FBQztBQUNGO0FBQ08sU0FBUyxLQUFLLENBQUMsUUFBUSxFQUFFLEtBQUssRUFBRSxJQUFJLEVBQUU7QUFDN0MsRUFBRSxJQUFJLENBQUMsR0FBRyxJQUFJLEtBQUssQ0FBQztBQUNwQixFQUFFLENBQUMsQ0FBQyxPQUFPLENBQUMsUUFBUSxFQUFFLEtBQUssRUFBRSxJQUFJLENBQUMsQ0FBQztBQUNuQyxFQUFFLE9BQU8sQ0FBQyxDQUFDO0FBQ1gsQ0FBQztBQUNEO0FBQ08sU0FBUyxVQUFVLEdBQUc7QUFDN0IsRUFBRSxHQUFHLEVBQUUsQ0FBQztBQUNSLEVBQUUsRUFBRSxLQUFLLENBQUM7QUFDVixFQUFFLElBQUksQ0FBQyxHQUFHLFFBQVEsRUFBRSxDQUFDLENBQUM7QUFDdEIsRUFBRSxPQUFPLENBQUMsRUFBRTtBQUNaLElBQUksSUFBSSxDQUFDLENBQUMsR0FBRyxRQUFRLEdBQUcsQ0FBQyxDQUFDLEtBQUssS0FBSyxDQUFDLEVBQUUsQ0FBQyxDQUFDLEtBQUssQ0FBQyxJQUFJLENBQUMsU0FBUyxFQUFFLENBQUMsQ0FBQyxDQUFDO0FBQ2xFLElBQUksQ0FBQyxHQUFHLENBQUMsQ0FBQyxLQUFLLENBQUM7QUFDaEIsR0FBRztBQUNILEVBQUUsRUFBRSxLQUFLLENBQUM7QUFDVixDQUFDO0FBQ0Q7QUFDQSxTQUFTLElBQUksR0FBRztBQUNoQixFQUFFLFFBQVEsR0FBRyxDQUFDLFNBQVMsR0FBRyxLQUFLLENBQUMsR0FBRyxFQUFFLElBQUksU0FBUyxDQUFDO0FBQ25ELEVBQUUsS0FBSyxHQUFHQSxTQUFPLEdBQUcsQ0FBQyxDQUFDO0FBQ3RCLEVBQUUsSUFBSTtBQUNOLElBQUksVUFBVSxFQUFFLENBQUM7QUFDakIsR0FBRyxTQUFTO0FBQ1osSUFBSSxLQUFLLEdBQUcsQ0FBQyxDQUFDO0FBQ2QsSUFBSSxHQUFHLEVBQUUsQ0FBQztBQUNWLElBQUksUUFBUSxHQUFHLENBQUMsQ0FBQztBQUNqQixHQUFHO0FBQ0gsQ0FBQztBQUNEO0FBQ0EsU0FBUyxJQUFJLEdBQUc7QUFDaEIsRUFBRSxJQUFJLEdBQUcsR0FBRyxLQUFLLENBQUMsR0FBRyxFQUFFLEVBQUUsS0FBSyxHQUFHLEdBQUcsR0FBRyxTQUFTLENBQUM7QUFDakQsRUFBRSxJQUFJLEtBQUssR0FBRyxTQUFTLEVBQUUsU0FBUyxJQUFJLEtBQUssRUFBRSxTQUFTLEdBQUcsR0FBRyxDQUFDO0FBQzdELENBQUM7QUFDRDtBQUNBLFNBQVMsR0FBRyxHQUFHO0FBQ2YsRUFBRSxJQUFJLEVBQUUsRUFBRSxFQUFFLEdBQUcsUUFBUSxFQUFFLEVBQUUsRUFBRSxJQUFJLEdBQUcsUUFBUSxDQUFDO0FBQzdDLEVBQUUsT0FBTyxFQUFFLEVBQUU7QUFDYixJQUFJLElBQUksRUFBRSxDQUFDLEtBQUssRUFBRTtBQUNsQixNQUFNLElBQUksSUFBSSxHQUFHLEVBQUUsQ0FBQyxLQUFLLEVBQUUsSUFBSSxHQUFHLEVBQUUsQ0FBQyxLQUFLLENBQUM7QUFDM0MsTUFBTSxFQUFFLEdBQUcsRUFBRSxFQUFFLEVBQUUsR0FBRyxFQUFFLENBQUMsS0FBSyxDQUFDO0FBQzdCLEtBQUssTUFBTTtBQUNYLE1BQU0sRUFBRSxHQUFHLEVBQUUsQ0FBQyxLQUFLLEVBQUUsRUFBRSxDQUFDLEtBQUssR0FBRyxJQUFJLENBQUM7QUFDckMsTUFBTSxFQUFFLEdBQUcsRUFBRSxHQUFHLEVBQUUsQ0FBQyxLQUFLLEdBQUcsRUFBRSxHQUFHLFFBQVEsR0FBRyxFQUFFLENBQUM7QUFDOUMsS0FBSztBQUNMLEdBQUc7QUFDSCxFQUFFLFFBQVEsR0FBRyxFQUFFLENBQUM7QUFDaEIsRUFBRSxLQUFLLENBQUMsSUFBSSxDQUFDLENBQUM7QUFDZCxDQUFDO0FBQ0Q7QUFDQSxTQUFTLEtBQUssQ0FBQyxJQUFJLEVBQUU7QUFDckIsRUFBRSxJQUFJLEtBQUssRUFBRSxPQUFPO0FBQ3BCLEVBQUUsSUFBSUEsU0FBTyxFQUFFQSxTQUFPLEdBQUcsWUFBWSxDQUFDQSxTQUFPLENBQUMsQ0FBQztBQUMvQyxFQUFFLElBQUksS0FBSyxHQUFHLElBQUksR0FBRyxRQUFRLENBQUM7QUFDOUIsRUFBRSxJQUFJLEtBQUssR0FBRyxFQUFFLEVBQUU7QUFDbEIsSUFBSSxJQUFJLElBQUksR0FBRyxRQUFRLEVBQUVBLFNBQU8sR0FBRyxVQUFVLENBQUMsSUFBSSxFQUFFLElBQUksR0FBRyxLQUFLLENBQUMsR0FBRyxFQUFFLEdBQUcsU0FBUyxDQUFDLENBQUM7QUFDcEYsSUFBSSxJQUFJLFFBQVEsRUFBRSxRQUFRLEdBQUcsYUFBYSxDQUFDLFFBQVEsQ0FBQyxDQUFDO0FBQ3JELEdBQUcsTUFBTTtBQUNULElBQUksSUFBSSxDQUFDLFFBQVEsRUFBRSxTQUFTLEdBQUcsS0FBSyxDQUFDLEdBQUcsRUFBRSxFQUFFLFFBQVEsR0FBRyxXQUFXLENBQUMsSUFBSSxFQUFFLFNBQVMsQ0FBQyxDQUFDO0FBQ3BGLElBQUksS0FBSyxHQUFHLENBQUMsRUFBRSxRQUFRLENBQUMsSUFBSSxDQUFDLENBQUM7QUFDOUIsR0FBRztBQUNIOztBQzNHZSxnQkFBUSxDQUFDLFFBQVEsRUFBRSxLQUFLLEVBQUUsSUFBSSxFQUFFO0FBQy9DLEVBQUUsSUFBSSxDQUFDLEdBQUcsSUFBSSxLQUFLLENBQUM7QUFDcEIsRUFBRSxLQUFLLEdBQUcsS0FBSyxJQUFJLElBQUksR0FBRyxDQUFDLEdBQUcsQ0FBQyxLQUFLLENBQUM7QUFDckMsRUFBRSxDQUFDLENBQUMsT0FBTyxDQUFDLE9BQU8sSUFBSTtBQUN2QixJQUFJLENBQUMsQ0FBQyxJQUFJLEVBQUUsQ0FBQztBQUNiLElBQUksUUFBUSxDQUFDLE9BQU8sR0FBRyxLQUFLLENBQUMsQ0FBQztBQUM5QixHQUFHLEVBQUUsS0FBSyxFQUFFLElBQUksQ0FBQyxDQUFDO0FBQ2xCLEVBQUUsT0FBTyxDQUFDLENBQUM7QUFDWDs7QUNQQSxJQUFJLE9BQU8sR0FBRyxRQUFRLENBQUMsT0FBTyxFQUFFLEtBQUssRUFBRSxRQUFRLEVBQUUsV0FBVyxDQUFDLENBQUM7QUFDOUQsSUFBSSxVQUFVLEdBQUcsRUFBRSxDQUFDO0FBQ3BCO0FBQ08sSUFBSSxPQUFPLEdBQUcsQ0FBQyxDQUFDO0FBQ2hCLElBQUksU0FBUyxHQUFHLENBQUMsQ0FBQztBQUNsQixJQUFJLFFBQVEsR0FBRyxDQUFDLENBQUM7QUFDakIsSUFBSSxPQUFPLEdBQUcsQ0FBQyxDQUFDO0FBQ2hCLElBQUksT0FBTyxHQUFHLENBQUMsQ0FBQztBQUNoQixJQUFJLE1BQU0sR0FBRyxDQUFDLENBQUM7QUFDZixJQUFJLEtBQUssR0FBRyxDQUFDLENBQUM7QUFDckI7QUFDZSxpQkFBUSxDQUFDLElBQUksRUFBRSxJQUFJLEVBQUUsRUFBRSxFQUFFLEtBQUssRUFBRSxLQUFLLEVBQUUsTUFBTSxFQUFFO0FBQzlELEVBQUUsSUFBSSxTQUFTLEdBQUcsSUFBSSxDQUFDLFlBQVksQ0FBQztBQUNwQyxFQUFFLElBQUksQ0FBQyxTQUFTLEVBQUUsSUFBSSxDQUFDLFlBQVksR0FBRyxFQUFFLENBQUM7QUFDekMsT0FBTyxJQUFJLEVBQUUsSUFBSSxTQUFTLEVBQUUsT0FBTztBQUNuQyxFQUFFLE1BQU0sQ0FBQyxJQUFJLEVBQUUsRUFBRSxFQUFFO0FBQ25CLElBQUksSUFBSSxFQUFFLElBQUk7QUFDZCxJQUFJLEtBQUssRUFBRSxLQUFLO0FBQ2hCLElBQUksS0FBSyxFQUFFLEtBQUs7QUFDaEIsSUFBSSxFQUFFLEVBQUUsT0FBTztBQUNmLElBQUksS0FBSyxFQUFFLFVBQVU7QUFDckIsSUFBSSxJQUFJLEVBQUUsTUFBTSxDQUFDLElBQUk7QUFDckIsSUFBSSxLQUFLLEVBQUUsTUFBTSxDQUFDLEtBQUs7QUFDdkIsSUFBSSxRQUFRLEVBQUUsTUFBTSxDQUFDLFFBQVE7QUFDN0IsSUFBSSxJQUFJLEVBQUUsTUFBTSxDQUFDLElBQUk7QUFDckIsSUFBSSxLQUFLLEVBQUUsSUFBSTtBQUNmLElBQUksS0FBSyxFQUFFLE9BQU87QUFDbEIsR0FBRyxDQUFDLENBQUM7QUFDTCxDQUFDO0FBQ0Q7QUFDTyxTQUFTLElBQUksQ0FBQyxJQUFJLEVBQUUsRUFBRSxFQUFFO0FBQy9CLEVBQUUsSUFBSSxRQUFRLEdBQUcsR0FBRyxDQUFDLElBQUksRUFBRSxFQUFFLENBQUMsQ0FBQztBQUMvQixFQUFFLElBQUksUUFBUSxDQUFDLEtBQUssR0FBRyxPQUFPLEVBQUUsTUFBTSxJQUFJLEtBQUssQ0FBQyw2QkFBNkIsQ0FBQyxDQUFDO0FBQy9FLEVBQUUsT0FBTyxRQUFRLENBQUM7QUFDbEIsQ0FBQztBQUNEO0FBQ08sU0FBUyxHQUFHLENBQUMsSUFBSSxFQUFFLEVBQUUsRUFBRTtBQUM5QixFQUFFLElBQUksUUFBUSxHQUFHLEdBQUcsQ0FBQyxJQUFJLEVBQUUsRUFBRSxDQUFDLENBQUM7QUFDL0IsRUFBRSxJQUFJLFFBQVEsQ0FBQyxLQUFLLEdBQUcsT0FBTyxFQUFFLE1BQU0sSUFBSSxLQUFLLENBQUMsMkJBQTJCLENBQUMsQ0FBQztBQUM3RSxFQUFFLE9BQU8sUUFBUSxDQUFDO0FBQ2xCLENBQUM7QUFDRDtBQUNPLFNBQVMsR0FBRyxDQUFDLElBQUksRUFBRSxFQUFFLEVBQUU7QUFDOUIsRUFBRSxJQUFJLFFBQVEsR0FBRyxJQUFJLENBQUMsWUFBWSxDQUFDO0FBQ25DLEVBQUUsSUFBSSxDQUFDLFFBQVEsSUFBSSxFQUFFLFFBQVEsR0FBRyxRQUFRLENBQUMsRUFBRSxDQUFDLENBQUMsRUFBRSxNQUFNLElBQUksS0FBSyxDQUFDLHNCQUFzQixDQUFDLENBQUM7QUFDdkYsRUFBRSxPQUFPLFFBQVEsQ0FBQztBQUNsQixDQUFDO0FBQ0Q7QUFDQSxTQUFTLE1BQU0sQ0FBQyxJQUFJLEVBQUUsRUFBRSxFQUFFLElBQUksRUFBRTtBQUNoQyxFQUFFLElBQUksU0FBUyxHQUFHLElBQUksQ0FBQyxZQUFZO0FBQ25DLE1BQU0sS0FBSyxDQUFDO0FBQ1o7QUFDQTtBQUNBO0FBQ0EsRUFBRSxTQUFTLENBQUMsRUFBRSxDQUFDLEdBQUcsSUFBSSxDQUFDO0FBQ3ZCLEVBQUUsSUFBSSxDQUFDLEtBQUssR0FBRyxLQUFLLENBQUMsUUFBUSxFQUFFLENBQUMsRUFBRSxJQUFJLENBQUMsSUFBSSxDQUFDLENBQUM7QUFDN0M7QUFDQSxFQUFFLFNBQVMsUUFBUSxDQUFDLE9BQU8sRUFBRTtBQUM3QixJQUFJLElBQUksQ0FBQyxLQUFLLEdBQUcsU0FBUyxDQUFDO0FBQzNCLElBQUksSUFBSSxDQUFDLEtBQUssQ0FBQyxPQUFPLENBQUMsS0FBSyxFQUFFLElBQUksQ0FBQyxLQUFLLEVBQUUsSUFBSSxDQUFDLElBQUksQ0FBQyxDQUFDO0FBQ3JEO0FBQ0E7QUFDQSxJQUFJLElBQUksSUFBSSxDQUFDLEtBQUssSUFBSSxPQUFPLEVBQUUsS0FBSyxDQUFDLE9BQU8sR0FBRyxJQUFJLENBQUMsS0FBSyxDQUFDLENBQUM7QUFDM0QsR0FBRztBQUNIO0FBQ0EsRUFBRSxTQUFTLEtBQUssQ0FBQyxPQUFPLEVBQUU7QUFDMUIsSUFBSSxJQUFJLENBQUMsRUFBRSxDQUFDLEVBQUUsQ0FBQyxFQUFFLENBQUMsQ0FBQztBQUNuQjtBQUNBO0FBQ0EsSUFBSSxJQUFJLElBQUksQ0FBQyxLQUFLLEtBQUssU0FBUyxFQUFFLE9BQU8sSUFBSSxFQUFFLENBQUM7QUFDaEQ7QUFDQSxJQUFJLEtBQUssQ0FBQyxJQUFJLFNBQVMsRUFBRTtBQUN6QixNQUFNLENBQUMsR0FBRyxTQUFTLENBQUMsQ0FBQyxDQUFDLENBQUM7QUFDdkIsTUFBTSxJQUFJLENBQUMsQ0FBQyxJQUFJLEtBQUssSUFBSSxDQUFDLElBQUksRUFBRSxTQUFTO0FBQ3pDO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsTUFBTSxJQUFJLENBQUMsQ0FBQyxLQUFLLEtBQUssT0FBTyxFQUFFLE9BQU8sT0FBTyxDQUFDLEtBQUssQ0FBQyxDQUFDO0FBQ3JEO0FBQ0E7QUFDQSxNQUFNLElBQUksQ0FBQyxDQUFDLEtBQUssS0FBSyxPQUFPLEVBQUU7QUFDL0IsUUFBUSxDQUFDLENBQUMsS0FBSyxHQUFHLEtBQUssQ0FBQztBQUN4QixRQUFRLENBQUMsQ0FBQyxLQUFLLENBQUMsSUFBSSxFQUFFLENBQUM7QUFDdkIsUUFBUSxDQUFDLENBQUMsRUFBRSxDQUFDLElBQUksQ0FBQyxXQUFXLEVBQUUsSUFBSSxFQUFFLElBQUksQ0FBQyxRQUFRLEVBQUUsQ0FBQyxDQUFDLEtBQUssRUFBRSxDQUFDLENBQUMsS0FBSyxDQUFDLENBQUM7QUFDdEUsUUFBUSxPQUFPLFNBQVMsQ0FBQyxDQUFDLENBQUMsQ0FBQztBQUM1QixPQUFPO0FBQ1A7QUFDQTtBQUNBLFdBQVcsSUFBSSxDQUFDLENBQUMsR0FBRyxFQUFFLEVBQUU7QUFDeEIsUUFBUSxDQUFDLENBQUMsS0FBSyxHQUFHLEtBQUssQ0FBQztBQUN4QixRQUFRLENBQUMsQ0FBQyxLQUFLLENBQUMsSUFBSSxFQUFFLENBQUM7QUFDdkIsUUFBUSxDQUFDLENBQUMsRUFBRSxDQUFDLElBQUksQ0FBQyxRQUFRLEVBQUUsSUFBSSxFQUFFLElBQUksQ0FBQyxRQUFRLEVBQUUsQ0FBQyxDQUFDLEtBQUssRUFBRSxDQUFDLENBQUMsS0FBSyxDQUFDLENBQUM7QUFDbkUsUUFBUSxPQUFPLFNBQVMsQ0FBQyxDQUFDLENBQUMsQ0FBQztBQUM1QixPQUFPO0FBQ1AsS0FBSztBQUNMO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQSxJQUFJLE9BQU8sQ0FBQyxXQUFXO0FBQ3ZCLE1BQU0sSUFBSSxJQUFJLENBQUMsS0FBSyxLQUFLLE9BQU8sRUFBRTtBQUNsQyxRQUFRLElBQUksQ0FBQyxLQUFLLEdBQUcsT0FBTyxDQUFDO0FBQzdCLFFBQVEsSUFBSSxDQUFDLEtBQUssQ0FBQyxPQUFPLENBQUMsSUFBSSxFQUFFLElBQUksQ0FBQyxLQUFLLEVBQUUsSUFBSSxDQUFDLElBQUksQ0FBQyxDQUFDO0FBQ3hELFFBQVEsSUFBSSxDQUFDLE9BQU8sQ0FBQyxDQUFDO0FBQ3RCLE9BQU87QUFDUCxLQUFLLENBQUMsQ0FBQztBQUNQO0FBQ0E7QUFDQTtBQUNBLElBQUksSUFBSSxDQUFDLEtBQUssR0FBRyxRQUFRLENBQUM7QUFDMUIsSUFBSSxJQUFJLENBQUMsRUFBRSxDQUFDLElBQUksQ0FBQyxPQUFPLEVBQUUsSUFBSSxFQUFFLElBQUksQ0FBQyxRQUFRLEVBQUUsSUFBSSxDQUFDLEtBQUssRUFBRSxJQUFJLENBQUMsS0FBSyxDQUFDLENBQUM7QUFDdkUsSUFBSSxJQUFJLElBQUksQ0FBQyxLQUFLLEtBQUssUUFBUSxFQUFFLE9BQU87QUFDeEMsSUFBSSxJQUFJLENBQUMsS0FBSyxHQUFHLE9BQU8sQ0FBQztBQUN6QjtBQUNBO0FBQ0EsSUFBSSxLQUFLLEdBQUcsSUFBSSxLQUFLLENBQUMsQ0FBQyxHQUFHLElBQUksQ0FBQyxLQUFLLENBQUMsTUFBTSxDQUFDLENBQUM7QUFDN0MsSUFBSSxLQUFLLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQyxHQUFHLENBQUMsQ0FBQyxFQUFFLENBQUMsR0FBRyxDQUFDLEVBQUUsRUFBRSxDQUFDLEVBQUU7QUFDcEMsTUFBTSxJQUFJLENBQUMsR0FBRyxJQUFJLENBQUMsS0FBSyxDQUFDLENBQUMsQ0FBQyxDQUFDLEtBQUssQ0FBQyxJQUFJLENBQUMsSUFBSSxFQUFFLElBQUksQ0FBQyxRQUFRLEVBQUUsSUFBSSxDQUFDLEtBQUssRUFBRSxJQUFJLENBQUMsS0FBSyxDQUFDLEVBQUU7QUFDckYsUUFBUSxLQUFLLENBQUMsRUFBRSxDQUFDLENBQUMsR0FBRyxDQUFDLENBQUM7QUFDdkIsT0FBTztBQUNQLEtBQUs7QUFDTCxJQUFJLEtBQUssQ0FBQyxNQUFNLEdBQUcsQ0FBQyxHQUFHLENBQUMsQ0FBQztBQUN6QixHQUFHO0FBQ0g7QUFDQSxFQUFFLFNBQVMsSUFBSSxDQUFDLE9BQU8sRUFBRTtBQUN6QixJQUFJLElBQUksQ0FBQyxHQUFHLE9BQU8sR0FBRyxJQUFJLENBQUMsUUFBUSxHQUFHLElBQUksQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLElBQUksRUFBRSxPQUFPLEdBQUcsSUFBSSxDQUFDLFFBQVEsQ0FBQyxJQUFJLElBQUksQ0FBQyxLQUFLLENBQUMsT0FBTyxDQUFDLElBQUksQ0FBQyxFQUFFLElBQUksQ0FBQyxLQUFLLEdBQUcsTUFBTSxFQUFFLENBQUMsQ0FBQztBQUN4SSxRQUFRLENBQUMsR0FBRyxDQUFDLENBQUM7QUFDZCxRQUFRLENBQUMsR0FBRyxLQUFLLENBQUMsTUFBTSxDQUFDO0FBQ3pCO0FBQ0EsSUFBSSxPQUFPLEVBQUUsQ0FBQyxHQUFHLENBQUMsRUFBRTtBQUNwQixNQUFNLEtBQUssQ0FBQyxDQUFDLENBQUMsQ0FBQyxJQUFJLENBQUMsSUFBSSxFQUFFLENBQUMsQ0FBQyxDQUFDO0FBQzdCLEtBQUs7QUFDTDtBQUNBO0FBQ0EsSUFBSSxJQUFJLElBQUksQ0FBQyxLQUFLLEtBQUssTUFBTSxFQUFFO0FBQy9CLE1BQU0sSUFBSSxDQUFDLEVBQUUsQ0FBQyxJQUFJLENBQUMsS0FBSyxFQUFFLElBQUksRUFBRSxJQUFJLENBQUMsUUFBUSxFQUFFLElBQUksQ0FBQyxLQUFLLEVBQUUsSUFBSSxDQUFDLEtBQUssQ0FBQyxDQUFDO0FBQ3ZFLE1BQU0sSUFBSSxFQUFFLENBQUM7QUFDYixLQUFLO0FBQ0wsR0FBRztBQUNIO0FBQ0EsRUFBRSxTQUFTLElBQUksR0FBRztBQUNsQixJQUFJLElBQUksQ0FBQyxLQUFLLEdBQUcsS0FBSyxDQUFDO0FBQ3ZCLElBQUksSUFBSSxDQUFDLEtBQUssQ0FBQyxJQUFJLEVBQUUsQ0FBQztBQUN0QixJQUFJLE9BQU8sU0FBUyxDQUFDLEVBQUUsQ0FBQyxDQUFDO0FBQ3pCLElBQUksS0FBSyxJQUFJLENBQUMsSUFBSSxTQUFTLEVBQUUsT0FBTztBQUNwQyxJQUFJLE9BQU8sSUFBSSxDQUFDLFlBQVksQ0FBQztBQUM3QixHQUFHO0FBQ0g7O0FDdEplLGtCQUFRLENBQUMsSUFBSSxFQUFFLElBQUksRUFBRTtBQUNwQyxFQUFFLElBQUksU0FBUyxHQUFHLElBQUksQ0FBQyxZQUFZO0FBQ25DLE1BQU0sUUFBUTtBQUNkLE1BQU0sTUFBTTtBQUNaLE1BQU0sS0FBSyxHQUFHLElBQUk7QUFDbEIsTUFBTSxDQUFDLENBQUM7QUFDUjtBQUNBLEVBQUUsSUFBSSxDQUFDLFNBQVMsRUFBRSxPQUFPO0FBQ3pCO0FBQ0EsRUFBRSxJQUFJLEdBQUcsSUFBSSxJQUFJLElBQUksR0FBRyxJQUFJLEdBQUcsSUFBSSxHQUFHLEVBQUUsQ0FBQztBQUN6QztBQUNBLEVBQUUsS0FBSyxDQUFDLElBQUksU0FBUyxFQUFFO0FBQ3ZCLElBQUksSUFBSSxDQUFDLFFBQVEsR0FBRyxTQUFTLENBQUMsQ0FBQyxDQUFDLEVBQUUsSUFBSSxLQUFLLElBQUksRUFBRSxFQUFFLEtBQUssR0FBRyxLQUFLLENBQUMsQ0FBQyxTQUFTLEVBQUU7QUFDN0UsSUFBSSxNQUFNLEdBQUcsUUFBUSxDQUFDLEtBQUssR0FBRyxRQUFRLElBQUksUUFBUSxDQUFDLEtBQUssR0FBRyxNQUFNLENBQUM7QUFDbEUsSUFBSSxRQUFRLENBQUMsS0FBSyxHQUFHLEtBQUssQ0FBQztBQUMzQixJQUFJLFFBQVEsQ0FBQyxLQUFLLENBQUMsSUFBSSxFQUFFLENBQUM7QUFDMUIsSUFBSSxRQUFRLENBQUMsRUFBRSxDQUFDLElBQUksQ0FBQyxNQUFNLEdBQUcsV0FBVyxHQUFHLFFBQVEsRUFBRSxJQUFJLEVBQUUsSUFBSSxDQUFDLFFBQVEsRUFBRSxRQUFRLENBQUMsS0FBSyxFQUFFLFFBQVEsQ0FBQyxLQUFLLENBQUMsQ0FBQztBQUMzRyxJQUFJLE9BQU8sU0FBUyxDQUFDLENBQUMsQ0FBQyxDQUFDO0FBQ3hCLEdBQUc7QUFDSDtBQUNBLEVBQUUsSUFBSSxLQUFLLEVBQUUsT0FBTyxJQUFJLENBQUMsWUFBWSxDQUFDO0FBQ3RDOztBQ3JCZSw0QkFBUSxDQUFDLElBQUksRUFBRTtBQUM5QixFQUFFLE9BQU8sSUFBSSxDQUFDLElBQUksQ0FBQyxXQUFXO0FBQzlCLElBQUksU0FBUyxDQUFDLElBQUksRUFBRSxJQUFJLENBQUMsQ0FBQztBQUMxQixHQUFHLENBQUMsQ0FBQztBQUNMOztBQ0pBLFNBQVMsV0FBVyxDQUFDLEVBQUUsRUFBRSxJQUFJLEVBQUU7QUFDL0IsRUFBRSxJQUFJLE1BQU0sRUFBRSxNQUFNLENBQUM7QUFDckIsRUFBRSxPQUFPLFdBQVc7QUFDcEIsSUFBSSxJQUFJLFFBQVEsR0FBRyxHQUFHLENBQUMsSUFBSSxFQUFFLEVBQUUsQ0FBQztBQUNoQyxRQUFRLEtBQUssR0FBRyxRQUFRLENBQUMsS0FBSyxDQUFDO0FBQy9CO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsSUFBSSxJQUFJLEtBQUssS0FBSyxNQUFNLEVBQUU7QUFDMUIsTUFBTSxNQUFNLEdBQUcsTUFBTSxHQUFHLEtBQUssQ0FBQztBQUM5QixNQUFNLEtBQUssSUFBSSxDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUMsR0FBRyxNQUFNLENBQUMsTUFBTSxFQUFFLENBQUMsR0FBRyxDQUFDLEVBQUUsRUFBRSxDQUFDLEVBQUU7QUFDckQsUUFBUSxJQUFJLE1BQU0sQ0FBQyxDQUFDLENBQUMsQ0FBQyxJQUFJLEtBQUssSUFBSSxFQUFFO0FBQ3JDLFVBQVUsTUFBTSxHQUFHLE1BQU0sQ0FBQyxLQUFLLEVBQUUsQ0FBQztBQUNsQyxVQUFVLE1BQU0sQ0FBQyxNQUFNLENBQUMsQ0FBQyxFQUFFLENBQUMsQ0FBQyxDQUFDO0FBQzlCLFVBQVUsTUFBTTtBQUNoQixTQUFTO0FBQ1QsT0FBTztBQUNQLEtBQUs7QUFDTDtBQUNBLElBQUksUUFBUSxDQUFDLEtBQUssR0FBRyxNQUFNLENBQUM7QUFDNUIsR0FBRyxDQUFDO0FBQ0osQ0FBQztBQUNEO0FBQ0EsU0FBUyxhQUFhLENBQUMsRUFBRSxFQUFFLElBQUksRUFBRSxLQUFLLEVBQUU7QUFDeEMsRUFBRSxJQUFJLE1BQU0sRUFBRSxNQUFNLENBQUM7QUFDckIsRUFBRSxJQUFJLE9BQU8sS0FBSyxLQUFLLFVBQVUsRUFBRSxNQUFNLElBQUksS0FBSyxDQUFDO0FBQ25ELEVBQUUsT0FBTyxXQUFXO0FBQ3BCLElBQUksSUFBSSxRQUFRLEdBQUcsR0FBRyxDQUFDLElBQUksRUFBRSxFQUFFLENBQUM7QUFDaEMsUUFBUSxLQUFLLEdBQUcsUUFBUSxDQUFDLEtBQUssQ0FBQztBQUMvQjtBQUNBO0FBQ0E7QUFDQTtBQUNBLElBQUksSUFBSSxLQUFLLEtBQUssTUFBTSxFQUFFO0FBQzFCLE1BQU0sTUFBTSxHQUFHLENBQUMsTUFBTSxHQUFHLEtBQUssRUFBRSxLQUFLLEVBQUUsQ0FBQztBQUN4QyxNQUFNLEtBQUssSUFBSSxDQUFDLEdBQUcsQ0FBQyxJQUFJLEVBQUUsSUFBSSxFQUFFLEtBQUssRUFBRSxLQUFLLENBQUMsRUFBRSxDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUMsR0FBRyxNQUFNLENBQUMsTUFBTSxFQUFFLENBQUMsR0FBRyxDQUFDLEVBQUUsRUFBRSxDQUFDLEVBQUU7QUFDckYsUUFBUSxJQUFJLE1BQU0sQ0FBQyxDQUFDLENBQUMsQ0FBQyxJQUFJLEtBQUssSUFBSSxFQUFFO0FBQ3JDLFVBQVUsTUFBTSxDQUFDLENBQUMsQ0FBQyxHQUFHLENBQUMsQ0FBQztBQUN4QixVQUFVLE1BQU07QUFDaEIsU0FBUztBQUNULE9BQU87QUFDUCxNQUFNLElBQUksQ0FBQyxLQUFLLENBQUMsRUFBRSxNQUFNLENBQUMsSUFBSSxDQUFDLENBQUMsQ0FBQyxDQUFDO0FBQ2xDLEtBQUs7QUFDTDtBQUNBLElBQUksUUFBUSxDQUFDLEtBQUssR0FBRyxNQUFNLENBQUM7QUFDNUIsR0FBRyxDQUFDO0FBQ0osQ0FBQztBQUNEO0FBQ2UseUJBQVEsQ0FBQyxJQUFJLEVBQUUsS0FBSyxFQUFFO0FBQ3JDLEVBQUUsSUFBSSxFQUFFLEdBQUcsSUFBSSxDQUFDLEdBQUcsQ0FBQztBQUNwQjtBQUNBLEVBQUUsSUFBSSxJQUFJLEVBQUUsQ0FBQztBQUNiO0FBQ0EsRUFBRSxJQUFJLFNBQVMsQ0FBQyxNQUFNLEdBQUcsQ0FBQyxFQUFFO0FBQzVCLElBQUksSUFBSSxLQUFLLEdBQUcsR0FBRyxDQUFDLElBQUksQ0FBQyxJQUFJLEVBQUUsRUFBRSxFQUFFLENBQUMsQ0FBQyxLQUFLLENBQUM7QUFDM0MsSUFBSSxLQUFLLElBQUksQ0FBQyxHQUFHLENBQUMsRUFBRSxDQUFDLEdBQUcsS0FBSyxDQUFDLE1BQU0sRUFBRSxDQUFDLEVBQUUsQ0FBQyxHQUFHLENBQUMsRUFBRSxFQUFFLENBQUMsRUFBRTtBQUNyRCxNQUFNLElBQUksQ0FBQyxDQUFDLEdBQUcsS0FBSyxDQUFDLENBQUMsQ0FBQyxFQUFFLElBQUksS0FBSyxJQUFJLEVBQUU7QUFDeEMsUUFBUSxPQUFPLENBQUMsQ0FBQyxLQUFLLENBQUM7QUFDdkIsT0FBTztBQUNQLEtBQUs7QUFDTCxJQUFJLE9BQU8sSUFBSSxDQUFDO0FBQ2hCLEdBQUc7QUFDSDtBQUNBLEVBQUUsT0FBTyxJQUFJLENBQUMsSUFBSSxDQUFDLENBQUMsS0FBSyxJQUFJLElBQUksR0FBRyxXQUFXLEdBQUcsYUFBYSxFQUFFLEVBQUUsRUFBRSxJQUFJLEVBQUUsS0FBSyxDQUFDLENBQUMsQ0FBQztBQUNuRixDQUFDO0FBQ0Q7QUFDTyxTQUFTLFVBQVUsQ0FBQyxVQUFVLEVBQUUsSUFBSSxFQUFFLEtBQUssRUFBRTtBQUNwRCxFQUFFLElBQUksRUFBRSxHQUFHLFVBQVUsQ0FBQyxHQUFHLENBQUM7QUFDMUI7QUFDQSxFQUFFLFVBQVUsQ0FBQyxJQUFJLENBQUMsV0FBVztBQUM3QixJQUFJLElBQUksUUFBUSxHQUFHLEdBQUcsQ0FBQyxJQUFJLEVBQUUsRUFBRSxDQUFDLENBQUM7QUFDakMsSUFBSSxDQUFDLFFBQVEsQ0FBQyxLQUFLLEtBQUssUUFBUSxDQUFDLEtBQUssR0FBRyxFQUFFLENBQUMsRUFBRSxJQUFJLENBQUMsR0FBRyxLQUFLLENBQUMsS0FBSyxDQUFDLElBQUksRUFBRSxTQUFTLENBQUMsQ0FBQztBQUNuRixHQUFHLENBQUMsQ0FBQztBQUNMO0FBQ0EsRUFBRSxPQUFPLFNBQVMsSUFBSSxFQUFFO0FBQ3hCLElBQUksT0FBTyxHQUFHLENBQUMsSUFBSSxFQUFFLEVBQUUsQ0FBQyxDQUFDLEtBQUssQ0FBQyxJQUFJLENBQUMsQ0FBQztBQUNyQyxHQUFHLENBQUM7QUFDSjs7QUM3RWUsb0JBQVEsQ0FBQyxDQUFDLEVBQUUsQ0FBQyxFQUFFO0FBQzlCLEVBQUUsSUFBSSxDQUFDLENBQUM7QUFDUixFQUFFLE9BQU8sQ0FBQyxPQUFPLENBQUMsS0FBSyxRQUFRLEdBQUcsaUJBQWlCO0FBQ25ELFFBQVEsQ0FBQyxZQUFZLEtBQUssR0FBRyxjQUFjO0FBQzNDLFFBQVEsQ0FBQyxDQUFDLEdBQUcsS0FBSyxDQUFDLENBQUMsQ0FBQyxLQUFLLENBQUMsR0FBRyxDQUFDLEVBQUUsY0FBYztBQUMvQyxRQUFRLGlCQUFpQixFQUFFLENBQUMsRUFBRSxDQUFDLENBQUMsQ0FBQztBQUNqQzs7QUNKQSxTQUFTLFVBQVUsQ0FBQyxJQUFJLEVBQUU7QUFDMUIsRUFBRSxPQUFPLFdBQVc7QUFDcEIsSUFBSSxJQUFJLENBQUMsZUFBZSxDQUFDLElBQUksQ0FBQyxDQUFDO0FBQy9CLEdBQUcsQ0FBQztBQUNKLENBQUM7QUFDRDtBQUNBLFNBQVMsWUFBWSxDQUFDLFFBQVEsRUFBRTtBQUNoQyxFQUFFLE9BQU8sV0FBVztBQUNwQixJQUFJLElBQUksQ0FBQyxpQkFBaUIsQ0FBQyxRQUFRLENBQUMsS0FBSyxFQUFFLFFBQVEsQ0FBQyxLQUFLLENBQUMsQ0FBQztBQUMzRCxHQUFHLENBQUM7QUFDSixDQUFDO0FBQ0Q7QUFDQSxTQUFTLFlBQVksQ0FBQyxJQUFJLEVBQUUsV0FBVyxFQUFFLE1BQU0sRUFBRTtBQUNqRCxFQUFFLElBQUksUUFBUTtBQUNkLE1BQU0sT0FBTyxHQUFHLE1BQU0sR0FBRyxFQUFFO0FBQzNCLE1BQU0sWUFBWSxDQUFDO0FBQ25CLEVBQUUsT0FBTyxXQUFXO0FBQ3BCLElBQUksSUFBSSxPQUFPLEdBQUcsSUFBSSxDQUFDLFlBQVksQ0FBQyxJQUFJLENBQUMsQ0FBQztBQUMxQyxJQUFJLE9BQU8sT0FBTyxLQUFLLE9BQU8sR0FBRyxJQUFJO0FBQ3JDLFVBQVUsT0FBTyxLQUFLLFFBQVEsR0FBRyxZQUFZO0FBQzdDLFVBQVUsWUFBWSxHQUFHLFdBQVcsQ0FBQyxRQUFRLEdBQUcsT0FBTyxFQUFFLE1BQU0sQ0FBQyxDQUFDO0FBQ2pFLEdBQUcsQ0FBQztBQUNKLENBQUM7QUFDRDtBQUNBLFNBQVMsY0FBYyxDQUFDLFFBQVEsRUFBRSxXQUFXLEVBQUUsTUFBTSxFQUFFO0FBQ3ZELEVBQUUsSUFBSSxRQUFRO0FBQ2QsTUFBTSxPQUFPLEdBQUcsTUFBTSxHQUFHLEVBQUU7QUFDM0IsTUFBTSxZQUFZLENBQUM7QUFDbkIsRUFBRSxPQUFPLFdBQVc7QUFDcEIsSUFBSSxJQUFJLE9BQU8sR0FBRyxJQUFJLENBQUMsY0FBYyxDQUFDLFFBQVEsQ0FBQyxLQUFLLEVBQUUsUUFBUSxDQUFDLEtBQUssQ0FBQyxDQUFDO0FBQ3RFLElBQUksT0FBTyxPQUFPLEtBQUssT0FBTyxHQUFHLElBQUk7QUFDckMsVUFBVSxPQUFPLEtBQUssUUFBUSxHQUFHLFlBQVk7QUFDN0MsVUFBVSxZQUFZLEdBQUcsV0FBVyxDQUFDLFFBQVEsR0FBRyxPQUFPLEVBQUUsTUFBTSxDQUFDLENBQUM7QUFDakUsR0FBRyxDQUFDO0FBQ0osQ0FBQztBQUNEO0FBQ0EsU0FBUyxZQUFZLENBQUMsSUFBSSxFQUFFLFdBQVcsRUFBRSxLQUFLLEVBQUU7QUFDaEQsRUFBRSxJQUFJLFFBQVE7QUFDZCxNQUFNLFFBQVE7QUFDZCxNQUFNLFlBQVksQ0FBQztBQUNuQixFQUFFLE9BQU8sV0FBVztBQUNwQixJQUFJLElBQUksT0FBTyxFQUFFLE1BQU0sR0FBRyxLQUFLLENBQUMsSUFBSSxDQUFDLEVBQUUsT0FBTyxDQUFDO0FBQy9DLElBQUksSUFBSSxNQUFNLElBQUksSUFBSSxFQUFFLE9BQU8sS0FBSyxJQUFJLENBQUMsZUFBZSxDQUFDLElBQUksQ0FBQyxDQUFDO0FBQy9ELElBQUksT0FBTyxHQUFHLElBQUksQ0FBQyxZQUFZLENBQUMsSUFBSSxDQUFDLENBQUM7QUFDdEMsSUFBSSxPQUFPLEdBQUcsTUFBTSxHQUFHLEVBQUUsQ0FBQztBQUMxQixJQUFJLE9BQU8sT0FBTyxLQUFLLE9BQU8sR0FBRyxJQUFJO0FBQ3JDLFVBQVUsT0FBTyxLQUFLLFFBQVEsSUFBSSxPQUFPLEtBQUssUUFBUSxHQUFHLFlBQVk7QUFDckUsV0FBVyxRQUFRLEdBQUcsT0FBTyxFQUFFLFlBQVksR0FBRyxXQUFXLENBQUMsUUFBUSxHQUFHLE9BQU8sRUFBRSxNQUFNLENBQUMsQ0FBQyxDQUFDO0FBQ3ZGLEdBQUcsQ0FBQztBQUNKLENBQUM7QUFDRDtBQUNBLFNBQVMsY0FBYyxDQUFDLFFBQVEsRUFBRSxXQUFXLEVBQUUsS0FBSyxFQUFFO0FBQ3RELEVBQUUsSUFBSSxRQUFRO0FBQ2QsTUFBTSxRQUFRO0FBQ2QsTUFBTSxZQUFZLENBQUM7QUFDbkIsRUFBRSxPQUFPLFdBQVc7QUFDcEIsSUFBSSxJQUFJLE9BQU8sRUFBRSxNQUFNLEdBQUcsS0FBSyxDQUFDLElBQUksQ0FBQyxFQUFFLE9BQU8sQ0FBQztBQUMvQyxJQUFJLElBQUksTUFBTSxJQUFJLElBQUksRUFBRSxPQUFPLEtBQUssSUFBSSxDQUFDLGlCQUFpQixDQUFDLFFBQVEsQ0FBQyxLQUFLLEVBQUUsUUFBUSxDQUFDLEtBQUssQ0FBQyxDQUFDO0FBQzNGLElBQUksT0FBTyxHQUFHLElBQUksQ0FBQyxjQUFjLENBQUMsUUFBUSxDQUFDLEtBQUssRUFBRSxRQUFRLENBQUMsS0FBSyxDQUFDLENBQUM7QUFDbEUsSUFBSSxPQUFPLEdBQUcsTUFBTSxHQUFHLEVBQUUsQ0FBQztBQUMxQixJQUFJLE9BQU8sT0FBTyxLQUFLLE9BQU8sR0FBRyxJQUFJO0FBQ3JDLFVBQVUsT0FBTyxLQUFLLFFBQVEsSUFBSSxPQUFPLEtBQUssUUFBUSxHQUFHLFlBQVk7QUFDckUsV0FBVyxRQUFRLEdBQUcsT0FBTyxFQUFFLFlBQVksR0FBRyxXQUFXLENBQUMsUUFBUSxHQUFHLE9BQU8sRUFBRSxNQUFNLENBQUMsQ0FBQyxDQUFDO0FBQ3ZGLEdBQUcsQ0FBQztBQUNKLENBQUM7QUFDRDtBQUNlLHdCQUFRLENBQUMsSUFBSSxFQUFFLEtBQUssRUFBRTtBQUNyQyxFQUFFLElBQUksUUFBUSxHQUFHLFNBQVMsQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDLEdBQUcsUUFBUSxLQUFLLFdBQVcsR0FBR0MsdUJBQW9CLEdBQUcsV0FBVyxDQUFDO0FBQ3BHLEVBQUUsT0FBTyxJQUFJLENBQUMsU0FBUyxDQUFDLElBQUksRUFBRSxPQUFPLEtBQUssS0FBSyxVQUFVO0FBQ3pELFFBQVEsQ0FBQyxRQUFRLENBQUMsS0FBSyxHQUFHLGNBQWMsR0FBRyxZQUFZLEVBQUUsUUFBUSxFQUFFLENBQUMsRUFBRSxVQUFVLENBQUMsSUFBSSxFQUFFLE9BQU8sR0FBRyxJQUFJLEVBQUUsS0FBSyxDQUFDLENBQUM7QUFDOUcsUUFBUSxLQUFLLElBQUksSUFBSSxHQUFHLENBQUMsUUFBUSxDQUFDLEtBQUssR0FBRyxZQUFZLEdBQUcsVUFBVSxFQUFFLFFBQVEsQ0FBQztBQUM5RSxRQUFRLENBQUMsUUFBUSxDQUFDLEtBQUssR0FBRyxjQUFjLEdBQUcsWUFBWSxFQUFFLFFBQVEsRUFBRSxDQUFDLEVBQUUsS0FBSyxDQUFDLENBQUMsQ0FBQztBQUM5RTs7QUMzRUEsU0FBUyxlQUFlLENBQUMsSUFBSSxFQUFFLENBQUMsRUFBRTtBQUNsQyxFQUFFLE9BQU8sU0FBUyxDQUFDLEVBQUU7QUFDckIsSUFBSSxJQUFJLENBQUMsWUFBWSxDQUFDLElBQUksRUFBRSxDQUFDLENBQUMsSUFBSSxDQUFDLElBQUksRUFBRSxDQUFDLENBQUMsQ0FBQyxDQUFDO0FBQzdDLEdBQUcsQ0FBQztBQUNKLENBQUM7QUFDRDtBQUNBLFNBQVMsaUJBQWlCLENBQUMsUUFBUSxFQUFFLENBQUMsRUFBRTtBQUN4QyxFQUFFLE9BQU8sU0FBUyxDQUFDLEVBQUU7QUFDckIsSUFBSSxJQUFJLENBQUMsY0FBYyxDQUFDLFFBQVEsQ0FBQyxLQUFLLEVBQUUsUUFBUSxDQUFDLEtBQUssRUFBRSxDQUFDLENBQUMsSUFBSSxDQUFDLElBQUksRUFBRSxDQUFDLENBQUMsQ0FBQyxDQUFDO0FBQ3pFLEdBQUcsQ0FBQztBQUNKLENBQUM7QUFDRDtBQUNBLFNBQVMsV0FBVyxDQUFDLFFBQVEsRUFBRSxLQUFLLEVBQUU7QUFDdEMsRUFBRSxJQUFJLEVBQUUsRUFBRSxFQUFFLENBQUM7QUFDYixFQUFFLFNBQVMsS0FBSyxHQUFHO0FBQ25CLElBQUksSUFBSSxDQUFDLEdBQUcsS0FBSyxDQUFDLEtBQUssQ0FBQyxJQUFJLEVBQUUsU0FBUyxDQUFDLENBQUM7QUFDekMsSUFBSSxJQUFJLENBQUMsS0FBSyxFQUFFLEVBQUUsRUFBRSxHQUFHLENBQUMsRUFBRSxHQUFHLENBQUMsS0FBSyxpQkFBaUIsQ0FBQyxRQUFRLEVBQUUsQ0FBQyxDQUFDLENBQUM7QUFDbEUsSUFBSSxPQUFPLEVBQUUsQ0FBQztBQUNkLEdBQUc7QUFDSCxFQUFFLEtBQUssQ0FBQyxNQUFNLEdBQUcsS0FBSyxDQUFDO0FBQ3ZCLEVBQUUsT0FBTyxLQUFLLENBQUM7QUFDZixDQUFDO0FBQ0Q7QUFDQSxTQUFTLFNBQVMsQ0FBQyxJQUFJLEVBQUUsS0FBSyxFQUFFO0FBQ2hDLEVBQUUsSUFBSSxFQUFFLEVBQUUsRUFBRSxDQUFDO0FBQ2IsRUFBRSxTQUFTLEtBQUssR0FBRztBQUNuQixJQUFJLElBQUksQ0FBQyxHQUFHLEtBQUssQ0FBQyxLQUFLLENBQUMsSUFBSSxFQUFFLFNBQVMsQ0FBQyxDQUFDO0FBQ3pDLElBQUksSUFBSSxDQUFDLEtBQUssRUFBRSxFQUFFLEVBQUUsR0FBRyxDQUFDLEVBQUUsR0FBRyxDQUFDLEtBQUssZUFBZSxDQUFDLElBQUksRUFBRSxDQUFDLENBQUMsQ0FBQztBQUM1RCxJQUFJLE9BQU8sRUFBRSxDQUFDO0FBQ2QsR0FBRztBQUNILEVBQUUsS0FBSyxDQUFDLE1BQU0sR0FBRyxLQUFLLENBQUM7QUFDdkIsRUFBRSxPQUFPLEtBQUssQ0FBQztBQUNmLENBQUM7QUFDRDtBQUNlLDZCQUFRLENBQUMsSUFBSSxFQUFFLEtBQUssRUFBRTtBQUNyQyxFQUFFLElBQUksR0FBRyxHQUFHLE9BQU8sR0FBRyxJQUFJLENBQUM7QUFDM0IsRUFBRSxJQUFJLFNBQVMsQ0FBQyxNQUFNLEdBQUcsQ0FBQyxFQUFFLE9BQU8sQ0FBQyxHQUFHLEdBQUcsSUFBSSxDQUFDLEtBQUssQ0FBQyxHQUFHLENBQUMsS0FBSyxHQUFHLENBQUMsTUFBTSxDQUFDO0FBQ3pFLEVBQUUsSUFBSSxLQUFLLElBQUksSUFBSSxFQUFFLE9BQU8sSUFBSSxDQUFDLEtBQUssQ0FBQyxHQUFHLEVBQUUsSUFBSSxDQUFDLENBQUM7QUFDbEQsRUFBRSxJQUFJLE9BQU8sS0FBSyxLQUFLLFVBQVUsRUFBRSxNQUFNLElBQUksS0FBSyxDQUFDO0FBQ25ELEVBQUUsSUFBSSxRQUFRLEdBQUcsU0FBUyxDQUFDLElBQUksQ0FBQyxDQUFDO0FBQ2pDLEVBQUUsT0FBTyxJQUFJLENBQUMsS0FBSyxDQUFDLEdBQUcsRUFBRSxDQUFDLFFBQVEsQ0FBQyxLQUFLLEdBQUcsV0FBVyxHQUFHLFNBQVMsRUFBRSxRQUFRLEVBQUUsS0FBSyxDQUFDLENBQUMsQ0FBQztBQUN0Rjs7QUN6Q0EsU0FBUyxhQUFhLENBQUMsRUFBRSxFQUFFLEtBQUssRUFBRTtBQUNsQyxFQUFFLE9BQU8sV0FBVztBQUNwQixJQUFJLElBQUksQ0FBQyxJQUFJLEVBQUUsRUFBRSxDQUFDLENBQUMsS0FBSyxHQUFHLENBQUMsS0FBSyxDQUFDLEtBQUssQ0FBQyxJQUFJLEVBQUUsU0FBUyxDQUFDLENBQUM7QUFDekQsR0FBRyxDQUFDO0FBQ0osQ0FBQztBQUNEO0FBQ0EsU0FBUyxhQUFhLENBQUMsRUFBRSxFQUFFLEtBQUssRUFBRTtBQUNsQyxFQUFFLE9BQU8sS0FBSyxHQUFHLENBQUMsS0FBSyxFQUFFLFdBQVc7QUFDcEMsSUFBSSxJQUFJLENBQUMsSUFBSSxFQUFFLEVBQUUsQ0FBQyxDQUFDLEtBQUssR0FBRyxLQUFLLENBQUM7QUFDakMsR0FBRyxDQUFDO0FBQ0osQ0FBQztBQUNEO0FBQ2UseUJBQVEsQ0FBQyxLQUFLLEVBQUU7QUFDL0IsRUFBRSxJQUFJLEVBQUUsR0FBRyxJQUFJLENBQUMsR0FBRyxDQUFDO0FBQ3BCO0FBQ0EsRUFBRSxPQUFPLFNBQVMsQ0FBQyxNQUFNO0FBQ3pCLFFBQVEsSUFBSSxDQUFDLElBQUksQ0FBQyxDQUFDLE9BQU8sS0FBSyxLQUFLLFVBQVU7QUFDOUMsWUFBWSxhQUFhO0FBQ3pCLFlBQVksYUFBYSxFQUFFLEVBQUUsRUFBRSxLQUFLLENBQUMsQ0FBQztBQUN0QyxRQUFRLEdBQUcsQ0FBQyxJQUFJLENBQUMsSUFBSSxFQUFFLEVBQUUsRUFBRSxDQUFDLENBQUMsS0FBSyxDQUFDO0FBQ25DOztBQ3BCQSxTQUFTLGdCQUFnQixDQUFDLEVBQUUsRUFBRSxLQUFLLEVBQUU7QUFDckMsRUFBRSxPQUFPLFdBQVc7QUFDcEIsSUFBSSxHQUFHLENBQUMsSUFBSSxFQUFFLEVBQUUsQ0FBQyxDQUFDLFFBQVEsR0FBRyxDQUFDLEtBQUssQ0FBQyxLQUFLLENBQUMsSUFBSSxFQUFFLFNBQVMsQ0FBQyxDQUFDO0FBQzNELEdBQUcsQ0FBQztBQUNKLENBQUM7QUFDRDtBQUNBLFNBQVMsZ0JBQWdCLENBQUMsRUFBRSxFQUFFLEtBQUssRUFBRTtBQUNyQyxFQUFFLE9BQU8sS0FBSyxHQUFHLENBQUMsS0FBSyxFQUFFLFdBQVc7QUFDcEMsSUFBSSxHQUFHLENBQUMsSUFBSSxFQUFFLEVBQUUsQ0FBQyxDQUFDLFFBQVEsR0FBRyxLQUFLLENBQUM7QUFDbkMsR0FBRyxDQUFDO0FBQ0osQ0FBQztBQUNEO0FBQ2UsNEJBQVEsQ0FBQyxLQUFLLEVBQUU7QUFDL0IsRUFBRSxJQUFJLEVBQUUsR0FBRyxJQUFJLENBQUMsR0FBRyxDQUFDO0FBQ3BCO0FBQ0EsRUFBRSxPQUFPLFNBQVMsQ0FBQyxNQUFNO0FBQ3pCLFFBQVEsSUFBSSxDQUFDLElBQUksQ0FBQyxDQUFDLE9BQU8sS0FBSyxLQUFLLFVBQVU7QUFDOUMsWUFBWSxnQkFBZ0I7QUFDNUIsWUFBWSxnQkFBZ0IsRUFBRSxFQUFFLEVBQUUsS0FBSyxDQUFDLENBQUM7QUFDekMsUUFBUSxHQUFHLENBQUMsSUFBSSxDQUFDLElBQUksRUFBRSxFQUFFLEVBQUUsQ0FBQyxDQUFDLFFBQVEsQ0FBQztBQUN0Qzs7QUNwQkEsU0FBUyxZQUFZLENBQUMsRUFBRSxFQUFFLEtBQUssRUFBRTtBQUNqQyxFQUFFLElBQUksT0FBTyxLQUFLLEtBQUssVUFBVSxFQUFFLE1BQU0sSUFBSSxLQUFLLENBQUM7QUFDbkQsRUFBRSxPQUFPLFdBQVc7QUFDcEIsSUFBSSxHQUFHLENBQUMsSUFBSSxFQUFFLEVBQUUsQ0FBQyxDQUFDLElBQUksR0FBRyxLQUFLLENBQUM7QUFDL0IsR0FBRyxDQUFDO0FBQ0osQ0FBQztBQUNEO0FBQ2Usd0JBQVEsQ0FBQyxLQUFLLEVBQUU7QUFDL0IsRUFBRSxJQUFJLEVBQUUsR0FBRyxJQUFJLENBQUMsR0FBRyxDQUFDO0FBQ3BCO0FBQ0EsRUFBRSxPQUFPLFNBQVMsQ0FBQyxNQUFNO0FBQ3pCLFFBQVEsSUFBSSxDQUFDLElBQUksQ0FBQyxZQUFZLENBQUMsRUFBRSxFQUFFLEtBQUssQ0FBQyxDQUFDO0FBQzFDLFFBQVEsR0FBRyxDQUFDLElBQUksQ0FBQyxJQUFJLEVBQUUsRUFBRSxFQUFFLENBQUMsQ0FBQyxJQUFJLENBQUM7QUFDbEM7O0FDYkEsU0FBUyxXQUFXLENBQUMsRUFBRSxFQUFFLEtBQUssRUFBRTtBQUNoQyxFQUFFLE9BQU8sV0FBVztBQUNwQixJQUFJLElBQUksQ0FBQyxHQUFHLEtBQUssQ0FBQyxLQUFLLENBQUMsSUFBSSxFQUFFLFNBQVMsQ0FBQyxDQUFDO0FBQ3pDLElBQUksSUFBSSxPQUFPLENBQUMsS0FBSyxVQUFVLEVBQUUsTUFBTSxJQUFJLEtBQUssQ0FBQztBQUNqRCxJQUFJLEdBQUcsQ0FBQyxJQUFJLEVBQUUsRUFBRSxDQUFDLENBQUMsSUFBSSxHQUFHLENBQUMsQ0FBQztBQUMzQixHQUFHLENBQUM7QUFDSixDQUFDO0FBQ0Q7QUFDZSwrQkFBUSxDQUFDLEtBQUssRUFBRTtBQUMvQixFQUFFLElBQUksT0FBTyxLQUFLLEtBQUssVUFBVSxFQUFFLE1BQU0sSUFBSSxLQUFLLENBQUM7QUFDbkQsRUFBRSxPQUFPLElBQUksQ0FBQyxJQUFJLENBQUMsV0FBVyxDQUFDLElBQUksQ0FBQyxHQUFHLEVBQUUsS0FBSyxDQUFDLENBQUMsQ0FBQztBQUNqRDs7QUNWZSwwQkFBUSxDQUFDLEtBQUssRUFBRTtBQUMvQixFQUFFLElBQUksT0FBTyxLQUFLLEtBQUssVUFBVSxFQUFFLEtBQUssR0FBRyxPQUFPLENBQUMsS0FBSyxDQUFDLENBQUM7QUFDMUQ7QUFDQSxFQUFFLEtBQUssSUFBSSxNQUFNLEdBQUcsSUFBSSxDQUFDLE9BQU8sRUFBRSxDQUFDLEdBQUcsTUFBTSxDQUFDLE1BQU0sRUFBRSxTQUFTLEdBQUcsSUFBSSxLQUFLLENBQUMsQ0FBQyxDQUFDLEVBQUUsQ0FBQyxHQUFHLENBQUMsRUFBRSxDQUFDLEdBQUcsQ0FBQyxFQUFFLEVBQUUsQ0FBQyxFQUFFO0FBQ2xHLElBQUksS0FBSyxJQUFJLEtBQUssR0FBRyxNQUFNLENBQUMsQ0FBQyxDQUFDLEVBQUUsQ0FBQyxHQUFHLEtBQUssQ0FBQyxNQUFNLEVBQUUsUUFBUSxHQUFHLFNBQVMsQ0FBQyxDQUFDLENBQUMsR0FBRyxFQUFFLEVBQUUsSUFBSSxFQUFFLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQyxHQUFHLENBQUMsRUFBRSxFQUFFLENBQUMsRUFBRTtBQUN6RyxNQUFNLElBQUksQ0FBQyxJQUFJLEdBQUcsS0FBSyxDQUFDLENBQUMsQ0FBQyxLQUFLLEtBQUssQ0FBQyxJQUFJLENBQUMsSUFBSSxFQUFFLElBQUksQ0FBQyxRQUFRLEVBQUUsQ0FBQyxFQUFFLEtBQUssQ0FBQyxFQUFFO0FBQzFFLFFBQVEsUUFBUSxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsQ0FBQztBQUM1QixPQUFPO0FBQ1AsS0FBSztBQUNMLEdBQUc7QUFDSDtBQUNBLEVBQUUsT0FBTyxJQUFJLFVBQVUsQ0FBQyxTQUFTLEVBQUUsSUFBSSxDQUFDLFFBQVEsRUFBRSxJQUFJLENBQUMsS0FBSyxFQUFFLElBQUksQ0FBQyxHQUFHLENBQUMsQ0FBQztBQUN4RTs7QUNiZSx5QkFBUSxDQUFDLFVBQVUsRUFBRTtBQUNwQyxFQUFFLElBQUksVUFBVSxDQUFDLEdBQUcsS0FBSyxJQUFJLENBQUMsR0FBRyxFQUFFLE1BQU0sSUFBSSxLQUFLLENBQUM7QUFDbkQ7QUFDQSxFQUFFLEtBQUssSUFBSSxPQUFPLEdBQUcsSUFBSSxDQUFDLE9BQU8sRUFBRSxPQUFPLEdBQUcsVUFBVSxDQUFDLE9BQU8sRUFBRSxFQUFFLEdBQUcsT0FBTyxDQUFDLE1BQU0sRUFBRSxFQUFFLEdBQUcsT0FBTyxDQUFDLE1BQU0sRUFBRSxDQUFDLEdBQUcsSUFBSSxDQUFDLEdBQUcsQ0FBQyxFQUFFLEVBQUUsRUFBRSxDQUFDLEVBQUUsTUFBTSxHQUFHLElBQUksS0FBSyxDQUFDLEVBQUUsQ0FBQyxFQUFFLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQyxHQUFHLENBQUMsRUFBRSxFQUFFLENBQUMsRUFBRTtBQUM1SyxJQUFJLEtBQUssSUFBSSxNQUFNLEdBQUcsT0FBTyxDQUFDLENBQUMsQ0FBQyxFQUFFLE1BQU0sR0FBRyxPQUFPLENBQUMsQ0FBQyxDQUFDLEVBQUUsQ0FBQyxHQUFHLE1BQU0sQ0FBQyxNQUFNLEVBQUUsS0FBSyxHQUFHLE1BQU0sQ0FBQyxDQUFDLENBQUMsR0FBRyxJQUFJLEtBQUssQ0FBQyxDQUFDLENBQUMsRUFBRSxJQUFJLEVBQUUsQ0FBQyxHQUFHLENBQUMsRUFBRSxDQUFDLEdBQUcsQ0FBQyxFQUFFLEVBQUUsQ0FBQyxFQUFFO0FBQ3JJLE1BQU0sSUFBSSxJQUFJLEdBQUcsTUFBTSxDQUFDLENBQUMsQ0FBQyxJQUFJLE1BQU0sQ0FBQyxDQUFDLENBQUMsRUFBRTtBQUN6QyxRQUFRLEtBQUssQ0FBQyxDQUFDLENBQUMsR0FBRyxJQUFJLENBQUM7QUFDeEIsT0FBTztBQUNQLEtBQUs7QUFDTCxHQUFHO0FBQ0g7QUFDQSxFQUFFLE9BQU8sQ0FBQyxHQUFHLEVBQUUsRUFBRSxFQUFFLENBQUMsRUFBRTtBQUN0QixJQUFJLE1BQU0sQ0FBQyxDQUFDLENBQUMsR0FBRyxPQUFPLENBQUMsQ0FBQyxDQUFDLENBQUM7QUFDM0IsR0FBRztBQUNIO0FBQ0EsRUFBRSxPQUFPLElBQUksVUFBVSxDQUFDLE1BQU0sRUFBRSxJQUFJLENBQUMsUUFBUSxFQUFFLElBQUksQ0FBQyxLQUFLLEVBQUUsSUFBSSxDQUFDLEdBQUcsQ0FBQyxDQUFDO0FBQ3JFOztBQ2hCQSxTQUFTLEtBQUssQ0FBQyxJQUFJLEVBQUU7QUFDckIsRUFBRSxPQUFPLENBQUMsSUFBSSxHQUFHLEVBQUUsRUFBRSxJQUFJLEVBQUUsQ0FBQyxLQUFLLENBQUMsT0FBTyxDQUFDLENBQUMsS0FBSyxDQUFDLFNBQVMsQ0FBQyxFQUFFO0FBQzdELElBQUksSUFBSSxDQUFDLEdBQUcsQ0FBQyxDQUFDLE9BQU8sQ0FBQyxHQUFHLENBQUMsQ0FBQztBQUMzQixJQUFJLElBQUksQ0FBQyxJQUFJLENBQUMsRUFBRSxDQUFDLEdBQUcsQ0FBQyxDQUFDLEtBQUssQ0FBQyxDQUFDLEVBQUUsQ0FBQyxDQUFDLENBQUM7QUFDbEMsSUFBSSxPQUFPLENBQUMsQ0FBQyxJQUFJLENBQUMsS0FBSyxPQUFPLENBQUM7QUFDL0IsR0FBRyxDQUFDLENBQUM7QUFDTCxDQUFDO0FBQ0Q7QUFDQSxTQUFTLFVBQVUsQ0FBQyxFQUFFLEVBQUUsSUFBSSxFQUFFLFFBQVEsRUFBRTtBQUN4QyxFQUFFLElBQUksR0FBRyxFQUFFLEdBQUcsRUFBRSxHQUFHLEdBQUcsS0FBSyxDQUFDLElBQUksQ0FBQyxHQUFHLElBQUksR0FBRyxHQUFHLENBQUM7QUFDL0MsRUFBRSxPQUFPLFdBQVc7QUFDcEIsSUFBSSxJQUFJLFFBQVEsR0FBRyxHQUFHLENBQUMsSUFBSSxFQUFFLEVBQUUsQ0FBQztBQUNoQyxRQUFRLEVBQUUsR0FBRyxRQUFRLENBQUMsRUFBRSxDQUFDO0FBQ3pCO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsSUFBSSxJQUFJLEVBQUUsS0FBSyxHQUFHLEVBQUUsQ0FBQyxHQUFHLEdBQUcsQ0FBQyxHQUFHLEdBQUcsRUFBRSxFQUFFLElBQUksRUFBRSxFQUFFLEVBQUUsQ0FBQyxJQUFJLEVBQUUsUUFBUSxDQUFDLENBQUM7QUFDakU7QUFDQSxJQUFJLFFBQVEsQ0FBQyxFQUFFLEdBQUcsR0FBRyxDQUFDO0FBQ3RCLEdBQUcsQ0FBQztBQUNKLENBQUM7QUFDRDtBQUNlLHNCQUFRLENBQUMsSUFBSSxFQUFFLFFBQVEsRUFBRTtBQUN4QyxFQUFFLElBQUksRUFBRSxHQUFHLElBQUksQ0FBQyxHQUFHLENBQUM7QUFDcEI7QUFDQSxFQUFFLE9BQU8sU0FBUyxDQUFDLE1BQU0sR0FBRyxDQUFDO0FBQzdCLFFBQVEsR0FBRyxDQUFDLElBQUksQ0FBQyxJQUFJLEVBQUUsRUFBRSxFQUFFLENBQUMsQ0FBQyxFQUFFLENBQUMsRUFBRSxDQUFDLElBQUksQ0FBQztBQUN4QyxRQUFRLElBQUksQ0FBQyxJQUFJLENBQUMsVUFBVSxDQUFDLEVBQUUsRUFBRSxJQUFJLEVBQUUsUUFBUSxDQUFDLENBQUMsQ0FBQztBQUNsRDs7QUMvQkEsU0FBUyxjQUFjLENBQUMsRUFBRSxFQUFFO0FBQzVCLEVBQUUsT0FBTyxXQUFXO0FBQ3BCLElBQUksSUFBSSxNQUFNLEdBQUcsSUFBSSxDQUFDLFVBQVUsQ0FBQztBQUNqQyxJQUFJLEtBQUssSUFBSSxDQUFDLElBQUksSUFBSSxDQUFDLFlBQVksRUFBRSxJQUFJLENBQUMsQ0FBQyxLQUFLLEVBQUUsRUFBRSxPQUFPO0FBQzNELElBQUksSUFBSSxNQUFNLEVBQUUsTUFBTSxDQUFDLFdBQVcsQ0FBQyxJQUFJLENBQUMsQ0FBQztBQUN6QyxHQUFHLENBQUM7QUFDSixDQUFDO0FBQ0Q7QUFDZSwwQkFBUSxHQUFHO0FBQzFCLEVBQUUsT0FBTyxJQUFJLENBQUMsRUFBRSxDQUFDLFlBQVksRUFBRSxjQUFjLENBQUMsSUFBSSxDQUFDLEdBQUcsQ0FBQyxDQUFDLENBQUM7QUFDekQ7O0FDTmUsMEJBQVEsQ0FBQyxNQUFNLEVBQUU7QUFDaEMsRUFBRSxJQUFJLElBQUksR0FBRyxJQUFJLENBQUMsS0FBSztBQUN2QixNQUFNLEVBQUUsR0FBRyxJQUFJLENBQUMsR0FBRyxDQUFDO0FBQ3BCO0FBQ0EsRUFBRSxJQUFJLE9BQU8sTUFBTSxLQUFLLFVBQVUsRUFBRSxNQUFNLEdBQUcsUUFBUSxDQUFDLE1BQU0sQ0FBQyxDQUFDO0FBQzlEO0FBQ0EsRUFBRSxLQUFLLElBQUksTUFBTSxHQUFHLElBQUksQ0FBQyxPQUFPLEVBQUUsQ0FBQyxHQUFHLE1BQU0sQ0FBQyxNQUFNLEVBQUUsU0FBUyxHQUFHLElBQUksS0FBSyxDQUFDLENBQUMsQ0FBQyxFQUFFLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQyxHQUFHLENBQUMsRUFBRSxFQUFFLENBQUMsRUFBRTtBQUNsRyxJQUFJLEtBQUssSUFBSSxLQUFLLEdBQUcsTUFBTSxDQUFDLENBQUMsQ0FBQyxFQUFFLENBQUMsR0FBRyxLQUFLLENBQUMsTUFBTSxFQUFFLFFBQVEsR0FBRyxTQUFTLENBQUMsQ0FBQyxDQUFDLEdBQUcsSUFBSSxLQUFLLENBQUMsQ0FBQyxDQUFDLEVBQUUsSUFBSSxFQUFFLE9BQU8sRUFBRSxDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUMsR0FBRyxDQUFDLEVBQUUsRUFBRSxDQUFDLEVBQUU7QUFDNUgsTUFBTSxJQUFJLENBQUMsSUFBSSxHQUFHLEtBQUssQ0FBQyxDQUFDLENBQUMsTUFBTSxPQUFPLEdBQUcsTUFBTSxDQUFDLElBQUksQ0FBQyxJQUFJLEVBQUUsSUFBSSxDQUFDLFFBQVEsRUFBRSxDQUFDLEVBQUUsS0FBSyxDQUFDLENBQUMsRUFBRTtBQUN2RixRQUFRLElBQUksVUFBVSxJQUFJLElBQUksRUFBRSxPQUFPLENBQUMsUUFBUSxHQUFHLElBQUksQ0FBQyxRQUFRLENBQUM7QUFDakUsUUFBUSxRQUFRLENBQUMsQ0FBQyxDQUFDLEdBQUcsT0FBTyxDQUFDO0FBQzlCLFFBQVEsUUFBUSxDQUFDLFFBQVEsQ0FBQyxDQUFDLENBQUMsRUFBRSxJQUFJLEVBQUUsRUFBRSxFQUFFLENBQUMsRUFBRSxRQUFRLEVBQUUsR0FBRyxDQUFDLElBQUksRUFBRSxFQUFFLENBQUMsQ0FBQyxDQUFDO0FBQ3BFLE9BQU87QUFDUCxLQUFLO0FBQ0wsR0FBRztBQUNIO0FBQ0EsRUFBRSxPQUFPLElBQUksVUFBVSxDQUFDLFNBQVMsRUFBRSxJQUFJLENBQUMsUUFBUSxFQUFFLElBQUksRUFBRSxFQUFFLENBQUMsQ0FBQztBQUM1RDs7QUNqQmUsNkJBQVEsQ0FBQyxNQUFNLEVBQUU7QUFDaEMsRUFBRSxJQUFJLElBQUksR0FBRyxJQUFJLENBQUMsS0FBSztBQUN2QixNQUFNLEVBQUUsR0FBRyxJQUFJLENBQUMsR0FBRyxDQUFDO0FBQ3BCO0FBQ0EsRUFBRSxJQUFJLE9BQU8sTUFBTSxLQUFLLFVBQVUsRUFBRSxNQUFNLEdBQUcsV0FBVyxDQUFDLE1BQU0sQ0FBQyxDQUFDO0FBQ2pFO0FBQ0EsRUFBRSxLQUFLLElBQUksTUFBTSxHQUFHLElBQUksQ0FBQyxPQUFPLEVBQUUsQ0FBQyxHQUFHLE1BQU0sQ0FBQyxNQUFNLEVBQUUsU0FBUyxHQUFHLEVBQUUsRUFBRSxPQUFPLEdBQUcsRUFBRSxFQUFFLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQyxHQUFHLENBQUMsRUFBRSxFQUFFLENBQUMsRUFBRTtBQUN0RyxJQUFJLEtBQUssSUFBSSxLQUFLLEdBQUcsTUFBTSxDQUFDLENBQUMsQ0FBQyxFQUFFLENBQUMsR0FBRyxLQUFLLENBQUMsTUFBTSxFQUFFLElBQUksRUFBRSxDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUMsR0FBRyxDQUFDLEVBQUUsRUFBRSxDQUFDLEVBQUU7QUFDM0UsTUFBTSxJQUFJLElBQUksR0FBRyxLQUFLLENBQUMsQ0FBQyxDQUFDLEVBQUU7QUFDM0IsUUFBUSxLQUFLLElBQUksUUFBUSxHQUFHLE1BQU0sQ0FBQyxJQUFJLENBQUMsSUFBSSxFQUFFLElBQUksQ0FBQyxRQUFRLEVBQUUsQ0FBQyxFQUFFLEtBQUssQ0FBQyxFQUFFLEtBQUssRUFBRSxPQUFPLEdBQUcsR0FBRyxDQUFDLElBQUksRUFBRSxFQUFFLENBQUMsRUFBRSxDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUMsR0FBRyxRQUFRLENBQUMsTUFBTSxFQUFFLENBQUMsR0FBRyxDQUFDLEVBQUUsRUFBRSxDQUFDLEVBQUU7QUFDaEosVUFBVSxJQUFJLEtBQUssR0FBRyxRQUFRLENBQUMsQ0FBQyxDQUFDLEVBQUU7QUFDbkMsWUFBWSxRQUFRLENBQUMsS0FBSyxFQUFFLElBQUksRUFBRSxFQUFFLEVBQUUsQ0FBQyxFQUFFLFFBQVEsRUFBRSxPQUFPLENBQUMsQ0FBQztBQUM1RCxXQUFXO0FBQ1gsU0FBUztBQUNULFFBQVEsU0FBUyxDQUFDLElBQUksQ0FBQyxRQUFRLENBQUMsQ0FBQztBQUNqQyxRQUFRLE9BQU8sQ0FBQyxJQUFJLENBQUMsSUFBSSxDQUFDLENBQUM7QUFDM0IsT0FBTztBQUNQLEtBQUs7QUFDTCxHQUFHO0FBQ0g7QUFDQSxFQUFFLE9BQU8sSUFBSSxVQUFVLENBQUMsU0FBUyxFQUFFLE9BQU8sRUFBRSxJQUFJLEVBQUUsRUFBRSxDQUFDLENBQUM7QUFDdEQ7O0FDdkJBLElBQUksU0FBUyxHQUFHLFNBQVMsQ0FBQyxTQUFTLENBQUMsV0FBVyxDQUFDO0FBQ2hEO0FBQ2UsNkJBQVEsR0FBRztBQUMxQixFQUFFLE9BQU8sSUFBSSxTQUFTLENBQUMsSUFBSSxDQUFDLE9BQU8sRUFBRSxJQUFJLENBQUMsUUFBUSxDQUFDLENBQUM7QUFDcEQ7O0FDQUEsU0FBUyxTQUFTLENBQUMsSUFBSSxFQUFFLFdBQVcsRUFBRTtBQUN0QyxFQUFFLElBQUksUUFBUTtBQUNkLE1BQU0sUUFBUTtBQUNkLE1BQU0sWUFBWSxDQUFDO0FBQ25CLEVBQUUsT0FBTyxXQUFXO0FBQ3BCLElBQUksSUFBSSxPQUFPLEdBQUdDLFVBQUssQ0FBQyxJQUFJLEVBQUUsSUFBSSxDQUFDO0FBQ25DLFFBQVEsT0FBTyxJQUFJLElBQUksQ0FBQyxLQUFLLENBQUMsY0FBYyxDQUFDLElBQUksQ0FBQyxFQUFFQSxVQUFLLENBQUMsSUFBSSxFQUFFLElBQUksQ0FBQyxDQUFDLENBQUM7QUFDdkUsSUFBSSxPQUFPLE9BQU8sS0FBSyxPQUFPLEdBQUcsSUFBSTtBQUNyQyxVQUFVLE9BQU8sS0FBSyxRQUFRLElBQUksT0FBTyxLQUFLLFFBQVEsR0FBRyxZQUFZO0FBQ3JFLFVBQVUsWUFBWSxHQUFHLFdBQVcsQ0FBQyxRQUFRLEdBQUcsT0FBTyxFQUFFLFFBQVEsR0FBRyxPQUFPLENBQUMsQ0FBQztBQUM3RSxHQUFHLENBQUM7QUFDSixDQUFDO0FBQ0Q7QUFDQSxTQUFTLFdBQVcsQ0FBQyxJQUFJLEVBQUU7QUFDM0IsRUFBRSxPQUFPLFdBQVc7QUFDcEIsSUFBSSxJQUFJLENBQUMsS0FBSyxDQUFDLGNBQWMsQ0FBQyxJQUFJLENBQUMsQ0FBQztBQUNwQyxHQUFHLENBQUM7QUFDSixDQUFDO0FBQ0Q7QUFDQSxTQUFTLGFBQWEsQ0FBQyxJQUFJLEVBQUUsV0FBVyxFQUFFLE1BQU0sRUFBRTtBQUNsRCxFQUFFLElBQUksUUFBUTtBQUNkLE1BQU0sT0FBTyxHQUFHLE1BQU0sR0FBRyxFQUFFO0FBQzNCLE1BQU0sWUFBWSxDQUFDO0FBQ25CLEVBQUUsT0FBTyxXQUFXO0FBQ3BCLElBQUksSUFBSSxPQUFPLEdBQUdBLFVBQUssQ0FBQyxJQUFJLEVBQUUsSUFBSSxDQUFDLENBQUM7QUFDcEMsSUFBSSxPQUFPLE9BQU8sS0FBSyxPQUFPLEdBQUcsSUFBSTtBQUNyQyxVQUFVLE9BQU8sS0FBSyxRQUFRLEdBQUcsWUFBWTtBQUM3QyxVQUFVLFlBQVksR0FBRyxXQUFXLENBQUMsUUFBUSxHQUFHLE9BQU8sRUFBRSxNQUFNLENBQUMsQ0FBQztBQUNqRSxHQUFHLENBQUM7QUFDSixDQUFDO0FBQ0Q7QUFDQSxTQUFTLGFBQWEsQ0FBQyxJQUFJLEVBQUUsV0FBVyxFQUFFLEtBQUssRUFBRTtBQUNqRCxFQUFFLElBQUksUUFBUTtBQUNkLE1BQU0sUUFBUTtBQUNkLE1BQU0sWUFBWSxDQUFDO0FBQ25CLEVBQUUsT0FBTyxXQUFXO0FBQ3BCLElBQUksSUFBSSxPQUFPLEdBQUdBLFVBQUssQ0FBQyxJQUFJLEVBQUUsSUFBSSxDQUFDO0FBQ25DLFFBQVEsTUFBTSxHQUFHLEtBQUssQ0FBQyxJQUFJLENBQUM7QUFDNUIsUUFBUSxPQUFPLEdBQUcsTUFBTSxHQUFHLEVBQUUsQ0FBQztBQUM5QixJQUFJLElBQUksTUFBTSxJQUFJLElBQUksRUFBRSxPQUFPLEdBQUcsTUFBTSxJQUFJLElBQUksQ0FBQyxLQUFLLENBQUMsY0FBYyxDQUFDLElBQUksQ0FBQyxFQUFFQSxVQUFLLENBQUMsSUFBSSxFQUFFLElBQUksQ0FBQyxDQUFDLENBQUM7QUFDaEcsSUFBSSxPQUFPLE9BQU8sS0FBSyxPQUFPLEdBQUcsSUFBSTtBQUNyQyxVQUFVLE9BQU8sS0FBSyxRQUFRLElBQUksT0FBTyxLQUFLLFFBQVEsR0FBRyxZQUFZO0FBQ3JFLFdBQVcsUUFBUSxHQUFHLE9BQU8sRUFBRSxZQUFZLEdBQUcsV0FBVyxDQUFDLFFBQVEsR0FBRyxPQUFPLEVBQUUsTUFBTSxDQUFDLENBQUMsQ0FBQztBQUN2RixHQUFHLENBQUM7QUFDSixDQUFDO0FBQ0Q7QUFDQSxTQUFTLGdCQUFnQixDQUFDLEVBQUUsRUFBRSxJQUFJLEVBQUU7QUFDcEMsRUFBRSxJQUFJLEdBQUcsRUFBRSxHQUFHLEVBQUUsU0FBUyxFQUFFLEdBQUcsR0FBRyxRQUFRLEdBQUcsSUFBSSxFQUFFLEtBQUssR0FBRyxNQUFNLEdBQUcsR0FBRyxFQUFFLE1BQU0sQ0FBQztBQUMvRSxFQUFFLE9BQU8sV0FBVztBQUNwQixJQUFJLElBQUksUUFBUSxHQUFHLEdBQUcsQ0FBQyxJQUFJLEVBQUUsRUFBRSxDQUFDO0FBQ2hDLFFBQVEsRUFBRSxHQUFHLFFBQVEsQ0FBQyxFQUFFO0FBQ3hCLFFBQVEsUUFBUSxHQUFHLFFBQVEsQ0FBQyxLQUFLLENBQUMsR0FBRyxDQUFDLElBQUksSUFBSSxHQUFHLE1BQU0sS0FBSyxNQUFNLEdBQUcsV0FBVyxDQUFDLElBQUksQ0FBQyxDQUFDLEdBQUcsU0FBUyxDQUFDO0FBQ3BHO0FBQ0E7QUFDQTtBQUNBO0FBQ0EsSUFBSSxJQUFJLEVBQUUsS0FBSyxHQUFHLElBQUksU0FBUyxLQUFLLFFBQVEsRUFBRSxDQUFDLEdBQUcsR0FBRyxDQUFDLEdBQUcsR0FBRyxFQUFFLEVBQUUsSUFBSSxFQUFFLEVBQUUsRUFBRSxDQUFDLEtBQUssRUFBRSxTQUFTLEdBQUcsUUFBUSxDQUFDLENBQUM7QUFDeEc7QUFDQSxJQUFJLFFBQVEsQ0FBQyxFQUFFLEdBQUcsR0FBRyxDQUFDO0FBQ3RCLEdBQUcsQ0FBQztBQUNKLENBQUM7QUFDRDtBQUNlLHlCQUFRLENBQUMsSUFBSSxFQUFFLEtBQUssRUFBRSxRQUFRLEVBQUU7QUFDL0MsRUFBRSxJQUFJLENBQUMsR0FBRyxDQUFDLElBQUksSUFBSSxFQUFFLE1BQU0sV0FBVyxHQUFHRCx1QkFBb0IsR0FBRyxXQUFXLENBQUM7QUFDNUUsRUFBRSxPQUFPLEtBQUssSUFBSSxJQUFJLEdBQUcsSUFBSTtBQUM3QixPQUFPLFVBQVUsQ0FBQyxJQUFJLEVBQUUsU0FBUyxDQUFDLElBQUksRUFBRSxDQUFDLENBQUMsQ0FBQztBQUMzQyxPQUFPLEVBQUUsQ0FBQyxZQUFZLEdBQUcsSUFBSSxFQUFFLFdBQVcsQ0FBQyxJQUFJLENBQUMsQ0FBQztBQUNqRCxNQUFNLE9BQU8sS0FBSyxLQUFLLFVBQVUsR0FBRyxJQUFJO0FBQ3hDLE9BQU8sVUFBVSxDQUFDLElBQUksRUFBRSxhQUFhLENBQUMsSUFBSSxFQUFFLENBQUMsRUFBRSxVQUFVLENBQUMsSUFBSSxFQUFFLFFBQVEsR0FBRyxJQUFJLEVBQUUsS0FBSyxDQUFDLENBQUMsQ0FBQztBQUN6RixPQUFPLElBQUksQ0FBQyxnQkFBZ0IsQ0FBQyxJQUFJLENBQUMsR0FBRyxFQUFFLElBQUksQ0FBQyxDQUFDO0FBQzdDLE1BQU0sSUFBSTtBQUNWLE9BQU8sVUFBVSxDQUFDLElBQUksRUFBRSxhQUFhLENBQUMsSUFBSSxFQUFFLENBQUMsRUFBRSxLQUFLLENBQUMsRUFBRSxRQUFRLENBQUM7QUFDaEUsT0FBTyxFQUFFLENBQUMsWUFBWSxHQUFHLElBQUksRUFBRSxJQUFJLENBQUMsQ0FBQztBQUNyQzs7QUMvRUEsU0FBUyxnQkFBZ0IsQ0FBQyxJQUFJLEVBQUUsQ0FBQyxFQUFFLFFBQVEsRUFBRTtBQUM3QyxFQUFFLE9BQU8sU0FBUyxDQUFDLEVBQUU7QUFDckIsSUFBSSxJQUFJLENBQUMsS0FBSyxDQUFDLFdBQVcsQ0FBQyxJQUFJLEVBQUUsQ0FBQyxDQUFDLElBQUksQ0FBQyxJQUFJLEVBQUUsQ0FBQyxDQUFDLEVBQUUsUUFBUSxDQUFDLENBQUM7QUFDNUQsR0FBRyxDQUFDO0FBQ0osQ0FBQztBQUNEO0FBQ0EsU0FBUyxVQUFVLENBQUMsSUFBSSxFQUFFLEtBQUssRUFBRSxRQUFRLEVBQUU7QUFDM0MsRUFBRSxJQUFJLENBQUMsRUFBRSxFQUFFLENBQUM7QUFDWixFQUFFLFNBQVMsS0FBSyxHQUFHO0FBQ25CLElBQUksSUFBSSxDQUFDLEdBQUcsS0FBSyxDQUFDLEtBQUssQ0FBQyxJQUFJLEVBQUUsU0FBUyxDQUFDLENBQUM7QUFDekMsSUFBSSxJQUFJLENBQUMsS0FBSyxFQUFFLEVBQUUsQ0FBQyxHQUFHLENBQUMsRUFBRSxHQUFHLENBQUMsS0FBSyxnQkFBZ0IsQ0FBQyxJQUFJLEVBQUUsQ0FBQyxFQUFFLFFBQVEsQ0FBQyxDQUFDO0FBQ3RFLElBQUksT0FBTyxDQUFDLENBQUM7QUFDYixHQUFHO0FBQ0gsRUFBRSxLQUFLLENBQUMsTUFBTSxHQUFHLEtBQUssQ0FBQztBQUN2QixFQUFFLE9BQU8sS0FBSyxDQUFDO0FBQ2YsQ0FBQztBQUNEO0FBQ2UsOEJBQVEsQ0FBQyxJQUFJLEVBQUUsS0FBSyxFQUFFLFFBQVEsRUFBRTtBQUMvQyxFQUFFLElBQUksR0FBRyxHQUFHLFFBQVEsSUFBSSxJQUFJLElBQUksRUFBRSxDQUFDLENBQUM7QUFDcEMsRUFBRSxJQUFJLFNBQVMsQ0FBQyxNQUFNLEdBQUcsQ0FBQyxFQUFFLE9BQU8sQ0FBQyxHQUFHLEdBQUcsSUFBSSxDQUFDLEtBQUssQ0FBQyxHQUFHLENBQUMsS0FBSyxHQUFHLENBQUMsTUFBTSxDQUFDO0FBQ3pFLEVBQUUsSUFBSSxLQUFLLElBQUksSUFBSSxFQUFFLE9BQU8sSUFBSSxDQUFDLEtBQUssQ0FBQyxHQUFHLEVBQUUsSUFBSSxDQUFDLENBQUM7QUFDbEQsRUFBRSxJQUFJLE9BQU8sS0FBSyxLQUFLLFVBQVUsRUFBRSxNQUFNLElBQUksS0FBSyxDQUFDO0FBQ25ELEVBQUUsT0FBTyxJQUFJLENBQUMsS0FBSyxDQUFDLEdBQUcsRUFBRSxVQUFVLENBQUMsSUFBSSxFQUFFLEtBQUssRUFBRSxRQUFRLElBQUksSUFBSSxHQUFHLEVBQUUsR0FBRyxRQUFRLENBQUMsQ0FBQyxDQUFDO0FBQ3BGOztBQ3JCQSxTQUFTLFlBQVksQ0FBQyxLQUFLLEVBQUU7QUFDN0IsRUFBRSxPQUFPLFdBQVc7QUFDcEIsSUFBSSxJQUFJLENBQUMsV0FBVyxHQUFHLEtBQUssQ0FBQztBQUM3QixHQUFHLENBQUM7QUFDSixDQUFDO0FBQ0Q7QUFDQSxTQUFTLFlBQVksQ0FBQyxLQUFLLEVBQUU7QUFDN0IsRUFBRSxPQUFPLFdBQVc7QUFDcEIsSUFBSSxJQUFJLE1BQU0sR0FBRyxLQUFLLENBQUMsSUFBSSxDQUFDLENBQUM7QUFDN0IsSUFBSSxJQUFJLENBQUMsV0FBVyxHQUFHLE1BQU0sSUFBSSxJQUFJLEdBQUcsRUFBRSxHQUFHLE1BQU0sQ0FBQztBQUNwRCxHQUFHLENBQUM7QUFDSixDQUFDO0FBQ0Q7QUFDZSx3QkFBUSxDQUFDLEtBQUssRUFBRTtBQUMvQixFQUFFLE9BQU8sSUFBSSxDQUFDLEtBQUssQ0FBQyxNQUFNLEVBQUUsT0FBTyxLQUFLLEtBQUssVUFBVTtBQUN2RCxRQUFRLFlBQVksQ0FBQyxVQUFVLENBQUMsSUFBSSxFQUFFLE1BQU0sRUFBRSxLQUFLLENBQUMsQ0FBQztBQUNyRCxRQUFRLFlBQVksQ0FBQyxLQUFLLElBQUksSUFBSSxHQUFHLEVBQUUsR0FBRyxLQUFLLEdBQUcsRUFBRSxDQUFDLENBQUMsQ0FBQztBQUN2RDs7QUNuQkEsU0FBUyxlQUFlLENBQUMsQ0FBQyxFQUFFO0FBQzVCLEVBQUUsT0FBTyxTQUFTLENBQUMsRUFBRTtBQUNyQixJQUFJLElBQUksQ0FBQyxXQUFXLEdBQUcsQ0FBQyxDQUFDLElBQUksQ0FBQyxJQUFJLEVBQUUsQ0FBQyxDQUFDLENBQUM7QUFDdkMsR0FBRyxDQUFDO0FBQ0osQ0FBQztBQUNEO0FBQ0EsU0FBUyxTQUFTLENBQUMsS0FBSyxFQUFFO0FBQzFCLEVBQUUsSUFBSSxFQUFFLEVBQUUsRUFBRSxDQUFDO0FBQ2IsRUFBRSxTQUFTLEtBQUssR0FBRztBQUNuQixJQUFJLElBQUksQ0FBQyxHQUFHLEtBQUssQ0FBQyxLQUFLLENBQUMsSUFBSSxFQUFFLFNBQVMsQ0FBQyxDQUFDO0FBQ3pDLElBQUksSUFBSSxDQUFDLEtBQUssRUFBRSxFQUFFLEVBQUUsR0FBRyxDQUFDLEVBQUUsR0FBRyxDQUFDLEtBQUssZUFBZSxDQUFDLENBQUMsQ0FBQyxDQUFDO0FBQ3RELElBQUksT0FBTyxFQUFFLENBQUM7QUFDZCxHQUFHO0FBQ0gsRUFBRSxLQUFLLENBQUMsTUFBTSxHQUFHLEtBQUssQ0FBQztBQUN2QixFQUFFLE9BQU8sS0FBSyxDQUFDO0FBQ2YsQ0FBQztBQUNEO0FBQ2UsNkJBQVEsQ0FBQyxLQUFLLEVBQUU7QUFDL0IsRUFBRSxJQUFJLEdBQUcsR0FBRyxNQUFNLENBQUM7QUFDbkIsRUFBRSxJQUFJLFNBQVMsQ0FBQyxNQUFNLEdBQUcsQ0FBQyxFQUFFLE9BQU8sQ0FBQyxHQUFHLEdBQUcsSUFBSSxDQUFDLEtBQUssQ0FBQyxHQUFHLENBQUMsS0FBSyxHQUFHLENBQUMsTUFBTSxDQUFDO0FBQ3pFLEVBQUUsSUFBSSxLQUFLLElBQUksSUFBSSxFQUFFLE9BQU8sSUFBSSxDQUFDLEtBQUssQ0FBQyxHQUFHLEVBQUUsSUFBSSxDQUFDLENBQUM7QUFDbEQsRUFBRSxJQUFJLE9BQU8sS0FBSyxLQUFLLFVBQVUsRUFBRSxNQUFNLElBQUksS0FBSyxDQUFDO0FBQ25ELEVBQUUsT0FBTyxJQUFJLENBQUMsS0FBSyxDQUFDLEdBQUcsRUFBRSxTQUFTLENBQUMsS0FBSyxDQUFDLENBQUMsQ0FBQztBQUMzQzs7QUNwQmUsOEJBQVEsR0FBRztBQUMxQixFQUFFLElBQUksSUFBSSxHQUFHLElBQUksQ0FBQyxLQUFLO0FBQ3ZCLE1BQU0sR0FBRyxHQUFHLElBQUksQ0FBQyxHQUFHO0FBQ3BCLE1BQU0sR0FBRyxHQUFHLEtBQUssRUFBRSxDQUFDO0FBQ3BCO0FBQ0EsRUFBRSxLQUFLLElBQUksTUFBTSxHQUFHLElBQUksQ0FBQyxPQUFPLEVBQUUsQ0FBQyxHQUFHLE1BQU0sQ0FBQyxNQUFNLEVBQUUsQ0FBQyxHQUFHLENBQUMsRUFBRSxDQUFDLEdBQUcsQ0FBQyxFQUFFLEVBQUUsQ0FBQyxFQUFFO0FBQ3hFLElBQUksS0FBSyxJQUFJLEtBQUssR0FBRyxNQUFNLENBQUMsQ0FBQyxDQUFDLEVBQUUsQ0FBQyxHQUFHLEtBQUssQ0FBQyxNQUFNLEVBQUUsSUFBSSxFQUFFLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQyxHQUFHLENBQUMsRUFBRSxFQUFFLENBQUMsRUFBRTtBQUMzRSxNQUFNLElBQUksSUFBSSxHQUFHLEtBQUssQ0FBQyxDQUFDLENBQUMsRUFBRTtBQUMzQixRQUFRLElBQUksT0FBTyxHQUFHLEdBQUcsQ0FBQyxJQUFJLEVBQUUsR0FBRyxDQUFDLENBQUM7QUFDckMsUUFBUSxRQUFRLENBQUMsSUFBSSxFQUFFLElBQUksRUFBRSxHQUFHLEVBQUUsQ0FBQyxFQUFFLEtBQUssRUFBRTtBQUM1QyxVQUFVLElBQUksRUFBRSxPQUFPLENBQUMsSUFBSSxHQUFHLE9BQU8sQ0FBQyxLQUFLLEdBQUcsT0FBTyxDQUFDLFFBQVE7QUFDL0QsVUFBVSxLQUFLLEVBQUUsQ0FBQztBQUNsQixVQUFVLFFBQVEsRUFBRSxPQUFPLENBQUMsUUFBUTtBQUNwQyxVQUFVLElBQUksRUFBRSxPQUFPLENBQUMsSUFBSTtBQUM1QixTQUFTLENBQUMsQ0FBQztBQUNYLE9BQU87QUFDUCxLQUFLO0FBQ0wsR0FBRztBQUNIO0FBQ0EsRUFBRSxPQUFPLElBQUksVUFBVSxDQUFDLE1BQU0sRUFBRSxJQUFJLENBQUMsUUFBUSxFQUFFLElBQUksRUFBRSxHQUFHLENBQUMsQ0FBQztBQUMxRDs7QUNyQmUsdUJBQVEsR0FBRztBQUMxQixFQUFFLElBQUksR0FBRyxFQUFFLEdBQUcsRUFBRSxJQUFJLEdBQUcsSUFBSSxFQUFFLEVBQUUsR0FBRyxJQUFJLENBQUMsR0FBRyxFQUFFLElBQUksR0FBRyxJQUFJLENBQUMsSUFBSSxFQUFFLENBQUM7QUFDL0QsRUFBRSxPQUFPLElBQUksT0FBTyxDQUFDLFNBQVMsT0FBTyxFQUFFLE1BQU0sRUFBRTtBQUMvQyxJQUFJLElBQUksTUFBTSxHQUFHLENBQUMsS0FBSyxFQUFFLE1BQU0sQ0FBQztBQUNoQyxRQUFRLEdBQUcsR0FBRyxDQUFDLEtBQUssRUFBRSxXQUFXLEVBQUUsSUFBSSxFQUFFLElBQUksS0FBSyxDQUFDLEVBQUUsT0FBTyxFQUFFLENBQUMsRUFBRSxDQUFDLENBQUM7QUFDbkU7QUFDQSxJQUFJLElBQUksQ0FBQyxJQUFJLENBQUMsV0FBVztBQUN6QixNQUFNLElBQUksUUFBUSxHQUFHLEdBQUcsQ0FBQyxJQUFJLEVBQUUsRUFBRSxDQUFDO0FBQ2xDLFVBQVUsRUFBRSxHQUFHLFFBQVEsQ0FBQyxFQUFFLENBQUM7QUFDM0I7QUFDQTtBQUNBO0FBQ0E7QUFDQSxNQUFNLElBQUksRUFBRSxLQUFLLEdBQUcsRUFBRTtBQUN0QixRQUFRLEdBQUcsR0FBRyxDQUFDLEdBQUcsR0FBRyxFQUFFLEVBQUUsSUFBSSxFQUFFLENBQUM7QUFDaEMsUUFBUSxHQUFHLENBQUMsQ0FBQyxDQUFDLE1BQU0sQ0FBQyxJQUFJLENBQUMsTUFBTSxDQUFDLENBQUM7QUFDbEMsUUFBUSxHQUFHLENBQUMsQ0FBQyxDQUFDLFNBQVMsQ0FBQyxJQUFJLENBQUMsTUFBTSxDQUFDLENBQUM7QUFDckMsUUFBUSxHQUFHLENBQUMsQ0FBQyxDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsR0FBRyxDQUFDLENBQUM7QUFDNUIsT0FBTztBQUNQO0FBQ0EsTUFBTSxRQUFRLENBQUMsRUFBRSxHQUFHLEdBQUcsQ0FBQztBQUN4QixLQUFLLENBQUMsQ0FBQztBQUNQO0FBQ0E7QUFDQSxJQUFJLElBQUksSUFBSSxLQUFLLENBQUMsRUFBRSxPQUFPLEVBQUUsQ0FBQztBQUM5QixHQUFHLENBQUMsQ0FBQztBQUNMOztBQ05BLElBQUksRUFBRSxHQUFHLENBQUMsQ0FBQztBQUNYO0FBQ08sU0FBUyxVQUFVLENBQUMsTUFBTSxFQUFFLE9BQU8sRUFBRSxJQUFJLEVBQUUsRUFBRSxFQUFFO0FBQ3RELEVBQUUsSUFBSSxDQUFDLE9BQU8sR0FBRyxNQUFNLENBQUM7QUFDeEIsRUFBRSxJQUFJLENBQUMsUUFBUSxHQUFHLE9BQU8sQ0FBQztBQUMxQixFQUFFLElBQUksQ0FBQyxLQUFLLEdBQUcsSUFBSSxDQUFDO0FBQ3BCLEVBQUUsSUFBSSxDQUFDLEdBQUcsR0FBRyxFQUFFLENBQUM7QUFDaEIsQ0FBQztBQUtEO0FBQ08sU0FBUyxLQUFLLEdBQUc7QUFDeEIsRUFBRSxPQUFPLEVBQUUsRUFBRSxDQUFDO0FBQ2QsQ0FBQztBQUNEO0FBQ0EsSUFBSSxtQkFBbUIsR0FBRyxTQUFTLENBQUMsU0FBUyxDQUFDO0FBQzlDO0FBQ0EsVUFBVSxDQUFDLFNBQVMsR0FBMEI7QUFDOUMsRUFBRSxXQUFXLEVBQUUsVUFBVTtBQUN6QixFQUFFLE1BQU0sRUFBRSxpQkFBaUI7QUFDM0IsRUFBRSxTQUFTLEVBQUUsb0JBQW9CO0FBQ2pDLEVBQUUsV0FBVyxFQUFFLG1CQUFtQixDQUFDLFdBQVc7QUFDOUMsRUFBRSxjQUFjLEVBQUUsbUJBQW1CLENBQUMsY0FBYztBQUNwRCxFQUFFLE1BQU0sRUFBRSxpQkFBaUI7QUFDM0IsRUFBRSxLQUFLLEVBQUUsZ0JBQWdCO0FBQ3pCLEVBQUUsU0FBUyxFQUFFLG9CQUFvQjtBQUNqQyxFQUFFLFVBQVUsRUFBRSxxQkFBcUI7QUFDbkMsRUFBRSxJQUFJLEVBQUUsbUJBQW1CLENBQUMsSUFBSTtBQUNoQyxFQUFFLEtBQUssRUFBRSxtQkFBbUIsQ0FBQyxLQUFLO0FBQ2xDLEVBQUUsSUFBSSxFQUFFLG1CQUFtQixDQUFDLElBQUk7QUFDaEMsRUFBRSxJQUFJLEVBQUUsbUJBQW1CLENBQUMsSUFBSTtBQUNoQyxFQUFFLEtBQUssRUFBRSxtQkFBbUIsQ0FBQyxLQUFLO0FBQ2xDLEVBQUUsSUFBSSxFQUFFLG1CQUFtQixDQUFDLElBQUk7QUFDaEMsRUFBRSxFQUFFLEVBQUUsYUFBYTtBQUNuQixFQUFFLElBQUksRUFBRSxlQUFlO0FBQ3ZCLEVBQUUsU0FBUyxFQUFFLG9CQUFvQjtBQUNqQyxFQUFFLEtBQUssRUFBRSxnQkFBZ0I7QUFDekIsRUFBRSxVQUFVLEVBQUUscUJBQXFCO0FBQ25DLEVBQUUsSUFBSSxFQUFFLGVBQWU7QUFDdkIsRUFBRSxTQUFTLEVBQUUsb0JBQW9CO0FBQ2pDLEVBQUUsTUFBTSxFQUFFLGlCQUFpQjtBQUMzQixFQUFFLEtBQUssRUFBRSxnQkFBZ0I7QUFDekIsRUFBRSxLQUFLLEVBQUUsZ0JBQWdCO0FBQ3pCLEVBQUUsUUFBUSxFQUFFLG1CQUFtQjtBQUMvQixFQUFFLElBQUksRUFBRSxlQUFlO0FBQ3ZCLEVBQUUsV0FBVyxFQUFFLHNCQUFzQjtBQUNyQyxFQUFFLEdBQUcsRUFBRSxjQUFjO0FBQ3JCLEVBQUUsQ0FBQyxNQUFNLENBQUMsUUFBUSxHQUFHLG1CQUFtQixDQUFDLE1BQU0sQ0FBQyxRQUFRLENBQUM7QUFDekQsQ0FBQzs7QUNoRU0sU0FBUyxVQUFVLENBQUMsQ0FBQyxFQUFFO0FBQzlCLEVBQUUsT0FBTyxDQUFDLENBQUMsQ0FBQyxJQUFJLENBQUMsS0FBSyxDQUFDLEdBQUcsQ0FBQyxHQUFHLENBQUMsR0FBRyxDQUFDLEdBQUcsQ0FBQyxDQUFDLElBQUksQ0FBQyxJQUFJLENBQUMsR0FBRyxDQUFDLEdBQUcsQ0FBQyxJQUFJLENBQUMsQ0FBQztBQUNoRTs7QUNMQSxJQUFJLGFBQWEsR0FBRztBQUNwQixFQUFFLElBQUksRUFBRSxJQUFJO0FBQ1osRUFBRSxLQUFLLEVBQUUsQ0FBQztBQUNWLEVBQUUsUUFBUSxFQUFFLEdBQUc7QUFDZixFQUFFLElBQUksRUFBRUUsVUFBYztBQUN0QixDQUFDLENBQUM7QUFDRjtBQUNBLFNBQVMsT0FBTyxDQUFDLElBQUksRUFBRSxFQUFFLEVBQUU7QUFDM0IsRUFBRSxJQUFJLE1BQU0sQ0FBQztBQUNiLEVBQUUsT0FBTyxFQUFFLE1BQU0sR0FBRyxJQUFJLENBQUMsWUFBWSxDQUFDLElBQUksRUFBRSxNQUFNLEdBQUcsTUFBTSxDQUFDLEVBQUUsQ0FBQyxDQUFDLEVBQUU7QUFDbEUsSUFBSSxJQUFJLEVBQUUsSUFBSSxHQUFHLElBQUksQ0FBQyxVQUFVLENBQUMsRUFBRTtBQUNuQyxNQUFNLE1BQU0sSUFBSSxLQUFLLENBQUMsQ0FBQyxXQUFXLEVBQUUsRUFBRSxDQUFDLFVBQVUsQ0FBQyxDQUFDLENBQUM7QUFDcEQsS0FBSztBQUNMLEdBQUc7QUFDSCxFQUFFLE9BQU8sTUFBTSxDQUFDO0FBQ2hCLENBQUM7QUFDRDtBQUNlLDZCQUFRLENBQUMsSUFBSSxFQUFFO0FBQzlCLEVBQUUsSUFBSSxFQUFFO0FBQ1IsTUFBTSxNQUFNLENBQUM7QUFDYjtBQUNBLEVBQUUsSUFBSSxJQUFJLFlBQVksVUFBVSxFQUFFO0FBQ2xDLElBQUksRUFBRSxHQUFHLElBQUksQ0FBQyxHQUFHLEVBQUUsSUFBSSxHQUFHLElBQUksQ0FBQyxLQUFLLENBQUM7QUFDckMsR0FBRyxNQUFNO0FBQ1QsSUFBSSxFQUFFLEdBQUcsS0FBSyxFQUFFLEVBQUUsQ0FBQyxNQUFNLEdBQUcsYUFBYSxFQUFFLElBQUksR0FBRyxHQUFHLEVBQUUsRUFBRSxJQUFJLEdBQUcsSUFBSSxJQUFJLElBQUksR0FBRyxJQUFJLEdBQUcsSUFBSSxHQUFHLEVBQUUsQ0FBQztBQUNoRyxHQUFHO0FBQ0g7QUFDQSxFQUFFLEtBQUssSUFBSSxNQUFNLEdBQUcsSUFBSSxDQUFDLE9BQU8sRUFBRSxDQUFDLEdBQUcsTUFBTSxDQUFDLE1BQU0sRUFBRSxDQUFDLEdBQUcsQ0FBQyxFQUFFLENBQUMsR0FBRyxDQUFDLEVBQUUsRUFBRSxDQUFDLEVBQUU7QUFDeEUsSUFBSSxLQUFLLElBQUksS0FBSyxHQUFHLE1BQU0sQ0FBQyxDQUFDLENBQUMsRUFBRSxDQUFDLEdBQUcsS0FBSyxDQUFDLE1BQU0sRUFBRSxJQUFJLEVBQUUsQ0FBQyxHQUFHLENBQUMsRUFBRSxDQUFDLEdBQUcsQ0FBQyxFQUFFLEVBQUUsQ0FBQyxFQUFFO0FBQzNFLE1BQU0sSUFBSSxJQUFJLEdBQUcsS0FBSyxDQUFDLENBQUMsQ0FBQyxFQUFFO0FBQzNCLFFBQVEsUUFBUSxDQUFDLElBQUksRUFBRSxJQUFJLEVBQUUsRUFBRSxFQUFFLENBQUMsRUFBRSxLQUFLLEVBQUUsTUFBTSxJQUFJLE9BQU8sQ0FBQyxJQUFJLEVBQUUsRUFBRSxDQUFDLENBQUMsQ0FBQztBQUN4RSxPQUFPO0FBQ1AsS0FBSztBQUNMLEdBQUc7QUFDSDtBQUNBLEVBQUUsT0FBTyxJQUFJLFVBQVUsQ0FBQyxNQUFNLEVBQUUsSUFBSSxDQUFDLFFBQVEsRUFBRSxJQUFJLEVBQUUsRUFBRSxDQUFDLENBQUM7QUFDekQ7O0FDckNBLFNBQVMsQ0FBQyxTQUFTLENBQUMsU0FBUyxHQUFHLG1CQUFtQixDQUFDO0FBQ3BELFNBQVMsQ0FBQyxTQUFTLENBQUMsVUFBVSxHQUFHLG9CQUFvQjs7QUNMckQsaUJBQWUsQ0FBQyxJQUFJLE1BQU0sQ0FBQzs7QUNBWixTQUFTLFNBQVMsQ0FBQyxJQUFJLEVBQUU7QUFDeEMsRUFBRSxXQUFXO0FBQ2IsRUFBRSxNQUFNO0FBQ1IsRUFBRSxTQUFTO0FBQ1gsRUFBRSxRQUFRO0FBQ1YsQ0FBQyxFQUFFO0FBQ0gsRUFBRSxNQUFNLENBQUMsZ0JBQWdCLENBQUMsSUFBSSxFQUFFO0FBQ2hDLElBQUksSUFBSSxFQUFFLENBQUMsS0FBSyxFQUFFLElBQUksRUFBRSxVQUFVLEVBQUUsSUFBSSxFQUFFLFlBQVksRUFBRSxJQUFJLENBQUM7QUFDN0QsSUFBSSxXQUFXLEVBQUUsQ0FBQyxLQUFLLEVBQUUsV0FBVyxFQUFFLFVBQVUsRUFBRSxJQUFJLEVBQUUsWUFBWSxFQUFFLElBQUksQ0FBQztBQUMzRSxJQUFJLE1BQU0sRUFBRSxDQUFDLEtBQUssRUFBRSxNQUFNLEVBQUUsVUFBVSxFQUFFLElBQUksRUFBRSxZQUFZLEVBQUUsSUFBSSxDQUFDO0FBQ2pFLElBQUksU0FBUyxFQUFFLENBQUMsS0FBSyxFQUFFLFNBQVMsRUFBRSxVQUFVLEVBQUUsSUFBSSxFQUFFLFlBQVksRUFBRSxJQUFJLENBQUM7QUFDdkUsSUFBSSxDQUFDLEVBQUUsQ0FBQyxLQUFLLEVBQUUsUUFBUSxDQUFDO0FBQ3hCLEdBQUcsQ0FBQyxDQUFDO0FBQ0w7O0FDYk8sU0FBUyxTQUFTLENBQUMsQ0FBQyxFQUFFLENBQUMsRUFBRSxDQUFDLEVBQUU7QUFDbkMsRUFBRSxJQUFJLENBQUMsQ0FBQyxHQUFHLENBQUMsQ0FBQztBQUNiLEVBQUUsSUFBSSxDQUFDLENBQUMsR0FBRyxDQUFDLENBQUM7QUFDYixFQUFFLElBQUksQ0FBQyxDQUFDLEdBQUcsQ0FBQyxDQUFDO0FBQ2IsQ0FBQztBQUNEO0FBQ0EsU0FBUyxDQUFDLFNBQVMsR0FBRztBQUN0QixFQUFFLFdBQVcsRUFBRSxTQUFTO0FBQ3hCLEVBQUUsS0FBSyxFQUFFLFNBQVMsQ0FBQyxFQUFFO0FBQ3JCLElBQUksT0FBTyxDQUFDLEtBQUssQ0FBQyxHQUFHLElBQUksR0FBRyxJQUFJLFNBQVMsQ0FBQyxJQUFJLENBQUMsQ0FBQyxHQUFHLENBQUMsRUFBRSxJQUFJLENBQUMsQ0FBQyxFQUFFLElBQUksQ0FBQyxDQUFDLENBQUMsQ0FBQztBQUN0RSxHQUFHO0FBQ0gsRUFBRSxTQUFTLEVBQUUsU0FBUyxDQUFDLEVBQUUsQ0FBQyxFQUFFO0FBQzVCLElBQUksT0FBTyxDQUFDLEtBQUssQ0FBQyxHQUFHLENBQUMsS0FBSyxDQUFDLEdBQUcsSUFBSSxHQUFHLElBQUksU0FBUyxDQUFDLElBQUksQ0FBQyxDQUFDLEVBQUUsSUFBSSxDQUFDLENBQUMsR0FBRyxJQUFJLENBQUMsQ0FBQyxHQUFHLENBQUMsRUFBRSxJQUFJLENBQUMsQ0FBQyxHQUFHLElBQUksQ0FBQyxDQUFDLEdBQUcsQ0FBQyxDQUFDLENBQUM7QUFDdEcsR0FBRztBQUNILEVBQUUsS0FBSyxFQUFFLFNBQVMsS0FBSyxFQUFFO0FBQ3pCLElBQUksT0FBTyxDQUFDLEtBQUssQ0FBQyxDQUFDLENBQUMsR0FBRyxJQUFJLENBQUMsQ0FBQyxHQUFHLElBQUksQ0FBQyxDQUFDLEVBQUUsS0FBSyxDQUFDLENBQUMsQ0FBQyxHQUFHLElBQUksQ0FBQyxDQUFDLEdBQUcsSUFBSSxDQUFDLENBQUMsQ0FBQyxDQUFDO0FBQ3BFLEdBQUc7QUFDSCxFQUFFLE1BQU0sRUFBRSxTQUFTLENBQUMsRUFBRTtBQUN0QixJQUFJLE9BQU8sQ0FBQyxHQUFHLElBQUksQ0FBQyxDQUFDLEdBQUcsSUFBSSxDQUFDLENBQUMsQ0FBQztBQUMvQixHQUFHO0FBQ0gsRUFBRSxNQUFNLEVBQUUsU0FBUyxDQUFDLEVBQUU7QUFDdEIsSUFBSSxPQUFPLENBQUMsR0FBRyxJQUFJLENBQUMsQ0FBQyxHQUFHLElBQUksQ0FBQyxDQUFDLENBQUM7QUFDL0IsR0FBRztBQUNILEVBQUUsTUFBTSxFQUFFLFNB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QUFFLENBQUMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxLQUFLLENBQUMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDLFNBQVM7QUFDNUUsUUFBUSxPQUFPLENBQUMsS0FBSyxVQUFVLEdBQUcsQ0FBQyxDQUFDLENBQUMsS0FBSyxDQUFDLElBQUksRUFBRSxTQUFTLENBQUMsR0FBRyxDQUFDLENBQUM7QUFDaEUsUUFBUSxPQUFPLENBQUMsS0FBSyxVQUFVLEdBQUcsQ0FBQyxDQUFDLENBQUMsS0FBSyxDQUFDLElBQUksRUFBRSxTQUFTLENBQUMsR0FBRyxDQUFDLENBQUM7QUFDaEUsT0FBTyxFQUFFLENBQUMsRUFBRSxlQUFlLENBQUMsQ0FBQztBQUM3QixLQUFLLEVBQUUsQ0FBQyxFQUFFLEtBQUssQ0FBQyxDQUFDO0FBQ2pCLEdBQUcsQ0FBQztBQUNKO0FBQ0EsRUFBRSxTQUFTLEtBQUssQ0FBQyxTQUFTLEVBQUUsQ0FBQyxFQUFFO0FBQy9CLElBQUksQ0FBQyxHQUFHLElBQUksQ0FBQyxHQUFHLENBQUMsV0FBVyxDQUFDLENBQUMsQ0FBQyxFQUFFLElBQUksQ0FBQyxHQUFHLENBQUMsV0FBVyxDQUFDLENBQUMsQ0FBQyxFQUFFLENBQUMsQ0FBQyxDQUFDLENBQUM7QUFDOUQsSUFBSSxPQUFPLENBQUMsS0FBSyxTQUFTLENBQUMsQ0FBQyxHQUFHLFNBQVMsR0FBRyxJQUFJLFNBQVMsQ0FBQyxDQUFDLEVBQUUsU0FBUyxDQUFDLENBQUMsRUFBRSxTQUFTLENBQUMsQ0FBQyxDQUFDLENBQUM7QUFDdEYsR0FBRztBQUNIO0FBQ0EsRUFBRSxTQUFTLFNBQVMsQ0FBQyxTQUFTLEVBQUUsRUFBRSxFQUFFLEVBQUUsRUFBRTtBQUN4QyxJQUFJLElBQUksQ0FBQyxHQUFHLEVBQUUsQ0FBQyxDQUFDLENBQUMsR0FBRyxFQUFFLENBQUMsQ0FBQyxDQUFDLEdBQUcsU0FBUyxDQUFDLENBQUMsRUFBRSxDQUFDLEdBQUcsRUFBRSxDQUFDLENBQUMsQ0FBQyxHQUFHLEVBQUUsQ0FBQyxDQUFDLENBQUMsR0FBRyxTQUFTLENB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QUFFLElBQUksQ0FBQyxDQUFDLEtBQUssQ0FBQyxLQUFLLENBQUM7QUFDNUMsUUFBUSxDQUFDLEdBQUcsSUFBSSxDQUFDLE1BQU07QUFDdkIsUUFBUSxDQUFDLEdBQUcsSUFBSSxDQUFDLEdBQUcsQ0FBQyxXQUFXLENBQUMsQ0FBQyxDQUFDLEVBQUUsSUFBSSxDQUFDLEdBQUcsQ0FBQyxXQUFXLENBQUMsQ0FBQyxDQUFDLEVBQUUsQ0FBQyxDQUFDLENBQUMsR0FBRyxJQUFJLENBQUMsR0FBRyxDQUFDLENBQUMsRUFBRSxVQUFVLENBQUMsS0FBSyxDQUFDLElBQUksRUFBRSxTQUFTLENBQUMsQ0FBQyxDQUFDLENBQUM7QUFDcEgsUUFBUSxDQUFDLEdBQUcsT0FBTyxDQUFDLEtBQUssQ0FBQyxDQUFDO0FBQzNCO0FBQ0E7QUFDQTtBQUNBLElBQUksSUFBSSxDQUFDLENBQUMsS0FBSyxFQUFFO0FBQ2pCLE1BQU0sSUFBSSxDQUFDLENBQUMsS0FBSyxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxLQUFLLENBQUMsQ0FBQyxDQUFDLENBQUMsSUFBSSxDQUFDLENBQUMsS0FBSyxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxLQUFLLENBQUMsQ0FBQyxDQUFDLENBQUMsRUFBRTtBQUM1RCxRQUFRLENBQUMsQ0FBQyxLQUFLLENBQUMsQ0FBQyxDQUFDLEdBQUcsQ0FBQyxDQUFDLE1BQU0sQ0FBQyxDQUFDLENBQUMsS0FBSyxDQUFDLENBQUMsQ0FBQyxHQUFHLENBQUMsQ0FBQyxDQUFDO0FBQzlDLE9BQU87QUFDUCxNQUFNLFlBQVksQ0FBQyxDQUFDLENBQUMsS0FBSyxDQUFDLENBQUM7QUFDNUIsS0FBSztBQUNMO0FBQ0E7QUFDQSxTQUFTLElBQUksQ0FBQyxDQUFDLENBQUMsS0FBSyxDQUFDLEVBQUUsT0FBTztBQUMvQjtBQUNBO0FBQ0EsU0FBUztBQUNULE1BQU0sQ0FBQyxDQUFDLEtBQUssR0FBRyxDQUFDLENBQUMsRUFBRSxDQUFDLENBQUMsTUFBTSxDQUFDLENBQUMsQ0FBQyxDQUFDLENB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QU87QUFDaEMsSUFBSSxJQUFJLENBQUMsR0FBRyxPQUFPLENBQUMsSUFBSSxFQUFFLElBQUksQ0FBQyxDQUFDLEtBQUssQ0FBQyxLQUFLLENBQUM7QUFDNUMsUUFBUSxPQUFPLEdBQUcsS0FBSyxDQUFDLGNBQWM7QUFDdEMsUUFBUSxDQUFDLEdBQUcsT0FBTyxDQUFDLE1BQU0sRUFBRSxDQUFDLEVBQUUsQ0FBQyxFQUFFLENBQUMsRUFBRSxDQUFDLENBQUM7QUFDdkM7QUFDQSxJQUFJLE9BQU8sQ0FBQyxLQUFLLENBQUMsQ0FBQztBQUNuQixJQUFJLEtBQUssQ0FBQyxHQUFHLENBQUMsRUFBRSxDQUFDLEdBQUcsQ0FBQyxFQUFFLEVBQUUsQ0FBQyxFQUFFO0FBQzVCLE1BQU0sQ0FBQyxHQUFHLE9BQU8sQ0FBQyxDQUFDLENBQUMsRUFBRSxDQUFDLEdBQUcsT0FBTyxDQUFDLENBQUMsRUFBRSxJQUFJLENBQUMsQ0FBQztBQUMzQyxNQUFNLElBQUksQ0FBQyxDQUFDLE1BQU0sSUFBSSxDQUFDLENBQUMsTUFBTSxDQUFDLENBQUMsQ0FBQyxLQUFLLENBQUMsQ0FBQyxVQUFVLEVBQUUsQ0FBQyxDQUFDLE1BQU0sQ0FBQyxDQUFDLENBQUMsR0FBRyxDQUFDLENBQUM7QUFDcEUsV0FBVyxJQUFJLENBQUMsQ0FBQyxNQUFNLElBQUksQ0FBQyxDQUFDLE1BQU0sQ0FBQyxDQUFDLENBQUMsS0FBSyxDQUFDLENBQUMsVUFBVSxFQUFFLENBQUMsQ0FBQyxNQUFNLENBQUMsQ0FBQyxDQUFDLEdBQUcsQ0FBQyxDQUFDO0FBQ3pFLEtBQUs7QUFDTCxJQUFJLENBQUMsR0FBRyxDQUFDLENBQUMsSUFBSSxDQUFDLE1BQU0sQ0FBQztBQUN0QixJQUFJLElBQUksQ0FBQyxDQUFDLE1BQU0sRUFBRTtBQUNsQixNQUFNLElBQUksRUFBRSxHQUFHLENBQUMsQ0FBQyxNQUFNLENBQUMsQ0FBQyxDQUFDLEVBQUUsRUFBRSxHQUFHLENBQUMsQ0FBQyxNQUFNLENBQUMsQ0FBQyxDQUFDO0FBQzVDLFVBQVUsRUFBRSxHQUFHLENBQUMsQ0FBQyxNQUFNLENBQUMsQ0FBQyxDQUFDLEVBQUUsRUFBRSxHQUFHLENBQUMsQ0FBQyxNQUFNLENBQUMsQ0FBQyxDQUFDO0FBQzVDLFVBQVUsRUFBRSxHQUFHLENBQUMsRUFBRSxHQUFHLEVBQUUsQ0FBQyxDQUFDLENBQUMsR0FBRyxFQUFFLENBQUMsQ0FBQyxDQUFDLElBQUksRUFBRSxHQUFHLENBQUMsRUFBRSxHQUFHLEVBQUUsQ0FBQyxDQUFDLENBQUMsR0FBRyxFQUFFLENBQUMsQ0FBQyxDQUFDLElBQUksRUFBRTtBQUNwRSxVQUFVLEVBQUUsR0FBRyxDQUFDLEVBQUUsR0FBRyxFQUFFLENBQUMsQ0FBQyxDQUFDLEdBQUcsRUFBRSxDQUFDLENBQUMsQ0FBQyxJQUFJLEVBQUUsR0FBRyxDQUFDLEVBQUUsR0FBRyxFQUFFLENBQUMsQ0FBQyxDQUFDLEdBQUcsRUFBRSxDQUFDLENBQUMsQ0FBQyxJQUFJLEVBQUUsQ0FBQztBQUNyRSxNQUFNLENBQUMsR0FBRyxLQUFLLENBQUMsQ0FBQyxFQUFFLElBQUksQ0FBQyxJQUFJLENBQUMsRUFBRSxHQUFHLEVBQUUsQ0FBQyxDQUFDLENBQUM7QUFDdkMsTUFBTSxDQUFDLEdBQUcsQ0FBQyxDQUFDLEVBQUUsQ0FBQyxDQUFDLENBQUMsR0FBRyxFQUFFLENBQUMsQ0FBQyxDQUFDLElBQUksQ0FBQyxFQUFFLENBQUMsRUFBRSxDQUFDLENBQUMsQ0FBQyxHQUFHLEVBQUUsQ0FBQyxDQUFDLENBQUMsSUFBSSxDQUFDLENBQUMsQ0FBQztBQUNyRCxNQUFNLENBQUMsR0FBRyxDQUFDLENBQUMsRUFBRSxDQUFDLENBQUMsQ0FBQyxHQUFHLEVBQUUsQ0FBQyxDQUFDLENBQUMsSUFBSSxDQUFDLEVBQUUsQ0FBQyxFQUFFLENBQUMsQ0FBQyxDQUFDLEdBQUcsRUFBRSxDQUFDLENBQUMsQ0FBQyxJQUFJLENBQUMsQ0FBQyxDQUFDO0FBQ3JELEtBQUs7QUFDTCxTQUFTLElBQUksQ0FBQyxDQUFDLE1BQU0sRUFBRSxDQUFDLEdBQUcsQ0FBQyxDQUFDLE1BQU0sQ0FBQyxDQUFD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Q0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDLEVBQUUsSUFBSSxJQUFJLE1BQU0sQ0FBQztBQUM3SSxHQUFHLENBQUM7QUFDSjtBQUNBLEVBQUUsSUFBSSxDQUFDLFdBQVcsR0FBRyxTQUFTLENBQUMsRUFBRTtBQUNqQyxJQUFJLE9BQU8sU0FBUyxDQUFDLE1BQU0sSUFBSSxXQUFXLENBQUMsQ0FBQyxDQUFDLEdBQUcsQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDLEVBQUUsV0FBVyxDQUFDLENBQUMsQ0FBQyxHQUFHLENBQUMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxFQUFFLElBQUksSUFBSSxDQUFDLFdBQVcsQ0FBQyxDQUFDLENBQUMsRUFBRSxXQUFXLENBQUMsQ0FBQyxDQUFDLENBQUMsQ0FBQztBQUN4SCxHQUFHLENBQUM7QUFDSjtBQUNBLEVBQUUsSUFBSSxDQUFDLGVBQWUsR0FBRyxTQUFTLENBQUMsRUFBRTtBQUNyQyxJQUFJLE9BQU8sU0FBUyxDQUFDLE1BQU0sSUFBSSxlQUFlLENBQUMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDLEdBQUcsQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDLEVBQUUsZUFBZSxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxHQUFHLENBQUMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxFQUFFLGVBQWUsQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUMsR0FBRyxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUMsRUFBRSxlQUFlLENBQUMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDLEdBQUcsQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDLEVBQUUsSUFBSSxJQUFJLENBQUMsQ0FBQyxlQUFlLENBQUMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxDQUFDLEVBQUUsZUFBZSxDQUFDLENBQUMsQ0FBQyxDQUFDLENBQUMsQ0FBQyxD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TSxJQUFJLGNBQWMsQ0FBQywyREFBMkQsQ0FBQyxDQUFDLEVBQUUsQ0FBQyxPQUFPLElBQUksS0FBSyxPQUFPLElBQUksS0FBSyxRQUFRLElBQUksT0FBTyxJQUFJLEtBQUssVUFBVSxDQUFDLEdBQUcsSUFBSSxHQUFHLElBQUksQ0FBQyxFQUFFO0FBQ2hQO0FBQ0EsQ0FBQSxTQUFTLFNBQVMsQ0FBQyxRQUFRLEVBQUUsVUFBVSxFQUFFLEVBQUUsSUFBSSxPQUFPLFVBQVUsS0FBSyxVQUFVLElBQUksVUFBVSxLQUFLLElBQUksRUFBRSxFQUFFLE1BQU0sSUFBSSxTQUFTLENBQUMsMERBQTBELEdBQUcsT0FBTyxVQUFVLENBQUMsQ0FBQyxFQUFFLENBQUMsUUFBUSxDQUFDLFNBQVMsR0FBRyxNQUFNLENBQUMsTUFBTSxDQUFDLFVBQVUsSUFBSSxVQUFVLENBQUMsU0FBUyxFQUFFLEVBQUUsV0FBVyxFQUFFLEVBQUUsS0FBSyxFQUFFLFFBQVEsRUFBRSxVQUFVLEVBQUUsS0FBSyxFQUFFLFFBQVEsRUFBRSxJQUFJLEVBQUUsWUFBWSxFQUFFLElBQUksRUFBRSxFQUFFLENBQUMsQ0FBQyxDQUFDLElBQUksVUFBVSxFQUFFLE1BQU0sQ0FBQyxjQUFjLEdBQUcsTUFBTSxDQUFDLGNBQWMsQ0FBQyxRQUFRLEVBQUUsVUFBVSxDQUFDLEdBQUcsUUFBUSxDQUFDLFNBQVMsR0FBRyxVQUFVLENBQUMsRUFBRTtBQUM5ZTtDQUNBLElBQUksTUFBTSxHQUFHLEVBQUUsQ0FBQztBQUNoQixDQUFBLElBQUksV0FBVyxDQUFDLGFBQWEsRUFBRSxNQUFNLENBQUMsSUFBSSxDQUFDLFdBQVcsQ0FBQyxhQUFhLENBQUMsQ0FBQztBQUN0RSxDQUFBLElBQUksV0FBVyxDQUFDLFlBQVksRUFBRSxNQUFNLENBQUMsSUFBSSxDQUFDLFdBQVcsQ0FBQyxZQUFZLENBQUMsQ0FBQztBQUNwRTtBQUNBLENBQUEsU0FBUyxjQUFjLENBQUMsSUFBSSxFQUFFLFFBQVEsRUFBRTtBQUN4QyxHQUFFLElBQUksTUFBTSxDQUFDLE1BQU0sRUFB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QUMsQ0FBQyxDQUFDLEdBQUcsR0FBRyxJQUFJLElBQUksQ0FBQyxHQUFHLEdBQUcsQ0FBQyxDQUFDLENBQUMsQ0FBQztBQUN4RixHQUFHO0FBQ0gsRUFBRSxhQUFhLEVBQUUsU0FBUyxFQUFFLEVBQUUsRUFBRSxFQUFFLEVBQUUsRUFBRSxFQUFFLEVBQUUsQ0FBQyxFQUFFLENBQUMsRUFBRTtBQUNoRCxJQUFJLElBQUksQ0FBQyxDQUFDLElBQUksR0FBRyxJQUFJLENBQUMsRUFBRSxDQUFDLEdBQUcsR0FBRyxJQUFJLENBQUMsRUFBRSxDQUFDLEdBQUcsR0FBRyxJQUFJLENBQUMsRUFBRSxDQUFDLEdBQUcsR0FBRyxJQUFJLENBQUMsRUFBRSxDQUFDLEdBQUcsR0FBRyxJQUFJLElBQUksQ0FBQyxHQUFHLEdBQUcsQ0FBQyxDQUFDLENBQUMsR0FBRyxHQUFHLElBQUksSUFBSSxDQUFDLEdBQUcsR0FBRyxDQUFDLENBQUMsQ0FBQyxDQUFDO0FBQ3BILEdBQUc7QUFDSCxFQUFFLEtBQUssRUFBRSxTQUFTLEVBQUUsRUFBRSxFQUFFLEVBQUUsRUFBRSxFQUFFLEVBQUUsRUFBRSxDQUFDLEVBQUU7QUFDckMsSUFBSSxFQUFFLEdBQUcsQ0FBQyxFQUFFLEVBQUUsRUFBRSxHQUFHLENBQUMsRUFBRSxFQUFFLEVBQUUsR0FBRyxDQUFDLEVBQUUsRUFBRSxFQUFFLEdBQUcsQ0FBQyxFQUFFLEVBQUUsQ0FBQyxHQUFHLENBQUMsQ0FBQyxDQUFDO0FBQ25ELElBQUksSUFBSSxFQUFFLEdBQUcsSUFBSSxDQUFDLEdBQUc7QUFDckIsUUFBUSxFQUFFLEdBQUcsSUFBSSxDQUFDLEdBQUc7QUFDckIsUUFBUSxHQUFHLEdBQUcsRUFBRSxHQUFHLEVBQUU7QUFDckIsUUFBUSxHQUFHLEdBQUcsRUFBRSxHQUFHLEVBQUU7QUFDckIsUUFBUSxHQUFHLEdBQUcsRUFBRSxHQUFHLEVBQUU7QUFDckIsUUFBUSxHQUFHLEdBQUcsRUFBRSxHQUFHLEVBQUU7QUFDckIsUUFBUSxLQUFLLEdBQUcsR0FBRyxHQUFHLEdBQUcsR0FBRyxH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LENBQUMsRUFBRSxDQUFDLEdBQUcsQ0FBQyxDQUFDLEVBQUUsQ0FBQyxHQUFHLENBQUMsQ0FBQyxFQUFFLEdBQUcsR0FBRyxDQUFDLENBQUMsR0FBRyxDQUFDO0FBQ3hDLElBQUksSUFBSSxFQUFFLEdBQUcsQ0FBQyxHQUFHLElBQUksQ0FBQyxHQUFHLENBQUMsRUFBRSxDQUFDO0FBQzdCLFFBQVEsRUFBRSxHQUFHLENBQUMsR0FBRyxJQUFJLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQztBQUM3QixRQUFRLEVBQUUsR0FBRyxDQUFDLEdBQUcsRUFBRTtBQUNuQixRQUFRLEVBQUUsR0FBRyxDQUFDLEdBQUcsRUFBRTtBQUNuQixRQUFRLEVBQUUsR0FBRyxDQUFDLEdBQUcsR0FBRztBQUNwQixRQUFRLEVBQUUsR0FBRyxHQUFHLEdBQUcsRUFBRSxHQUFHLEVBQUUsR0FBRyxFQUFFLEdBQUcsRUFBRSxDQUFDO0FBQ3JDO0FBQ0E7QUFDQSxJQUFJLElBQUksQ0FBQyxHQUFHLENBQUMsRUFBRSxNQUFNLElBQUksS0FBSyxDQUFDLG1CQUFtQixHQUFHLENBQUMsQ0FBQyxDQUFDO0FBQ3hEO0FBQ0E7QUFDQSxJQUFJLElBQUksSUFBSSxDQUFDLEdBQUcsS0FBSyxJQUFJLEVBQUU7QUFDM0IsTUFBTSxJQUFJLENBQUMsQ0FBQyxJQUFJLEdBQUcsR0FBRyxFQUFFLEdBQUcsR0FBRyxHQUFHLEVBQUUsQ0FBQztBQUNwQyxLQUFLO0FBQ0w7QUFDQTtBQUNBLFNBQVMsSUFBSSxJQUFJLENBQUMsR0FBRyxDQUFDLElBQUksQ0FBQyxHQUFHLEdBQUcsRUFBRSxDQUFDLEdBQUcsT0FBTyxJQUFJLElBQUksQ0FBQyxHQUFHLENBQUMsSUFBSSxDQUFDLEdBQUcsR0FBRyxFQUFFLENBQUMsR0FBRyxPQUFPLEVBQUU7QUFDckYsTUFBTSxJQUFJLENBQUMsQ0FBQyxJQUFJLEdBQUcsR0FBRyxFQUFFLEdBQUcsR0FBRyxHQUFHLEVBQUUsQ0FBQztBQUNwQyxLQUFLO0FBQ0w7QUFDQTtBQUNBLElBQUksSUFBSSxDQUFDLENBQUMsRUFBRSxPQUFPO0FBQ25CO0FBQ0E7QUFDQSxJQUFJLElBQUksRUFBRSxHQUFHLENBQUMsRUFBRSxFQUFFLEdBQUcsRUFBRSxHQUFHLEdBQUcsR0FBRyxHQUFHLENBQUM7QUFDcEM7QUFDQTtBQUNBLElBQUksSUFBSSxFQUFFLEdBQUcsVUFBVSxFQUFFO0FBQ3pCLE1BQU0sSUFBSSxDQUFDLENBQUMsSUFBSSxHQUFHLEdBQUcsQ0FBQyxHQUFHLEdBQUcsR0FBRyxDQUFDLEdBQUcsT0FBTyxHQUFHLEVBQUUsR0FBRyxHQUFHLElBQUksQ0FBQyxHQUFHLEVBQUUsQ0FBQyxHQUFHLEdBQUcsSUFBSSxDQUFDLEdBQUcsRUFBRSxDQUFDLEdBQUcsR0FBRyxHQUFHLENBQUMsR0FBRyxHQUFHLEdBQUcsQ0FBQyxHQUFHLE9BQU8sR0FBRyxFQUFFLEdBQUcsR0FBRyxJQUFJLElBQUksQ0FBQyxHQUFHLEdBQUcsRUFBRSxDQUFDLEdBQUcsR0FBRyxJQUFJLElBQUksQ0FBQyxHQUFHLEdBQUcsRUFBRSxDQUFDLENBQUM7QUFDdEssS0FBSztBQUNMO0FBQ0E7QUFDQSxTQUFTLElBQUksRUFBRSxHQUFHLE9BQU8sRUFBRTtBQUMzQixNQUFNLElBQUksQ0FBQyxDQUFDLElBQUksR0FBRyxHQUFHLENBQUMsR0FBRyxHQUFHLEdBQUcsQ0FBQyxHQUFHLEtBQUssSUFBSSxFQUFFLEVBQUUsSUFBSSxFQUFFLENBQUMsQ0FBQyxHQUFHLEdBQUcsR0FBRyxFQUFFLEdBQUcsR0FBRyxJQUFJLElBQUksQ0FBQyxHQUFHLEdBQUcsQ0FBQyxHQUFHLENBQUMsR0FBRyxJQUFJLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQyxDQUFDLEdBQUcsR0FBRyxJQUFJLElBQUksQ0FBQyxHQUFHLEdBQUcsQ0FBQyxHQUFHLENBQUMsR0FBRyxJQUFJLENBQUMsR0FBRyxDQUFDLEVBQUUsQ0FBQyxDQUFDLENBQUM7QUFDekosS0FBSztBQUNMLEdBQUc7QUFDSCxFQUFFLElBQUksRUFBRSxTQUFTLENBQUMsRUFBRSxDQUFDLEVBQUUsQ0FBQyxFQUFF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RUFBQSxRQUFBLEVBQUEsQ0FBQUMsR0FBQSxDQUFDLGdCQUFnQixDQUFDLFFBQVEsRUFBQSxRQUFBLENBQUEsRUFBQyxLQUFLLEVBQUksSUFBSSxFQUFBLEVBQUEsRUFBQSxRQUFBLEVBQ3JDQSxJQUFDLGlCQUFpQixFQUFBLEVBQUMsR0FBRyxFQUFFLEdBQUcsRUFBRSxJQUFJLEVBQUUsS0FBSyxDQUFDLElBQUksRUFBRSxDQUFDLEVBQUUsQ0FBQyxFQUFJLENBQUEsRUFBQSxDQUFBLENBQzlCLEVBQzVCQSxHQUFBLENBQUEsS0FBQSxFQUFBLEVBQUEsUUFBQSxFQUFNLFlBQVksQ0FBQyxHQUFHLENBQUMsVUFBQSxHQUFHLEVBQUssRUFBQSxPQUFPLENBQUMsR0FBRyxDQUFDLEdBQUcsQ0FBQyxDQUFDLENBQUMsT0FBT0EsR0FBd0IsQ0FBQSxHQUFBLEVBQUEsRUFBQSxRQUFBLEVBQUEsbUJBQUEsRUFBQSxDQUFBLENBQUEsRUFBQyxDQUFDLEVBQUEsQ0FBTyxDQUNwRixFQUFBLENBQUEsQ0FBQSxFQUFDO0FBQ1g7Ozs7In0=
