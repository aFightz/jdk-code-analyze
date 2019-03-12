package conllection;

import java.io.Serializable;
import java.lang.reflect.ParameterizedType;
import java.lang.reflect.Type;
import java.util.*;
import java.util.function.Consumer;

public class HashMapAnalyze <K,V> extends AbstractMap<K,V>
        implements Map<K,V>, Cloneable, Serializable {

    //容器默认的容量
    static final int DEFAULT_INITIAL_CAPACITY = 1 << 4; // aka 16

    //容器最大容量(如果超出会如何处理？)，大概是10亿7千万
    static final int MAXIMUM_CAPACITY = 1 << 30;


    static final float DEFAULT_LOAD_FACTOR = 0.75f;


    //CAPACITY * FACTOR = THRESHOLD`
    static final int TREEIFY_THRESHOLD = 8;


    transient HashMapAnalyze.Node<K,V>[] table;

    transient int modCount;

    int threshold;

    transient int size;

    static final int UNTREEIFY_THRESHOLD = 6;

    final float loadFactor;

    static final int MIN_TREEIFY_CAPACITY = 64;

    transient Set<Map.Entry<K,V>> entrySet;

    public HashMapAnalyze() {
        this.loadFactor = DEFAULT_LOAD_FACTOR; // all other fields defaulted
    }

    /**
     * 容器元素定义
     * @param <K>
     * @param <V>
     */
    static class Node<K,V> implements Map.Entry<K,V> {
        final int hash;
        final K key;
        V value;
        HashMapAnalyze.Node<K,V> next;

        Node(int hash, K key, V value, HashMapAnalyze.Node<K,V> next) {
            this.hash = hash;
            this.key = key;
            this.value = value;
            this.next = next;
        }

        public final K getKey()        { return key; }
        public final V getValue()      { return value; }
        public final String toString() { return key + "=" + value; }

        public final int hashCode() {
            return Objects.hashCode(key) ^ Objects.hashCode(value);
        }

        public final V setValue(V newValue) {
            V oldValue = value;
            value = newValue;
            return oldValue;
        }

        public final boolean equals(Object o) {
            if (o == this)
                return true;
            if (o instanceof Map.Entry) {
                Map.Entry<?,?> e = (Map.Entry<?,?>)o;
                if (Objects.equals(key, e.getKey()) &&
                        Objects.equals(value, e.getValue()))
                    return true;
            }
            return false;
        }
    }



    static final class TreeNode<K,V> extends HashMapAnalyze.Node<K,V> {
        HashMapAnalyze.TreeNode<K,V> parent;  // red-black tree links
        HashMapAnalyze.TreeNode<K,V> left;
        HashMapAnalyze.TreeNode<K,V> right;
        HashMapAnalyze.TreeNode<K,V> prev;    // needed to unlink next upon deletion
        boolean red;
        TreeNode(int hash, K key, V val, HashMapAnalyze.Node<K,V> next) {
            super(hash, key, val, next);
        }

        /**
         * Returns root of tree containing this node.
         */
        final HashMapAnalyze.TreeNode<K,V> root() {
            for (HashMapAnalyze.TreeNode<K,V> r = this, p;;) {
                if ((p = r.parent) == null)
                    return r;
                r = p;
            }
        }

        /**
         * Ensures that the given root is the first node of its bin.
         */
        static <K,V> void moveRootToFront(HashMapAnalyze.Node<K,V>[] tab, HashMapAnalyze.TreeNode<K,V> root) {
            int n;
            if (root != null && tab != null && (n = tab.length) > 0) {
                int index = (n - 1) & root.hash;
                HashMapAnalyze.TreeNode<K,V> first = (HashMapAnalyze.TreeNode<K,V>)tab[index];
                if (root != first) {
                    HashMapAnalyze.Node<K,V> rn;
                    tab[index] = root;
                    HashMapAnalyze.TreeNode<K,V> rp = root.prev;
                    if ((rn = root.next) != null)
                        ((HashMapAnalyze.TreeNode<K,V>)rn).prev = rp;
                    if (rp != null)
                        rp.next = rn;
                    if (first != null)
                        first.prev = root;
                    root.next = first;
                    root.prev = null;
                }
                assert checkInvariants(root);
            }
        }

        /**
         * Finds the node starting at root p with the given hash and key.
         * The kc argument caches comparableClassFor(key) upon first use
         * comparing keys.
         */
        final HashMapAnalyze.TreeNode<K,V> find(int h, Object k, Class<?> kc) {
            HashMapAnalyze.TreeNode<K,V> p = this;
            do {
                int ph, dir; K pk;
                HashMapAnalyze.TreeNode<K,V> pl = p.left, pr = p.right, q;
                if ((ph = p.hash) > h)
                    p = pl;
                else if (ph < h)
                    p = pr;
                else if ((pk = p.key) == k || (k != null && k.equals(pk)))
                    return p;
                else if (pl == null)
                    p = pr;
                else if (pr == null)
                    p = pl;
                else if ((kc != null ||
                        (kc = comparableClassFor(k)) != null) &&
                        (dir = compareComparables(kc, k, pk)) != 0)
                    p = (dir < 0) ? pl : pr;
                else if ((q = pr.find(h, k, kc)) != null)
                    return q;
                else
                    p = pl;
            } while (p != null);
            return null;
        }

        /**
         * Calls find for root node.
         */
        final HashMapAnalyze.TreeNode<K,V> getTreeNode(int h, Object k) {
            return ((parent != null) ? root() : this).find(h, k, null);
        }

        /**
         * Tie-breaking utility for ordering insertions when equal
         * hashCodes and non-comparable. We don't require a total
         * order, just a consistent insertion rule to maintain
         * equivalence across rebalancings. Tie-breaking further than
         * necessary simplifies testing a bit.
         */
        static int tieBreakOrder(Object a, Object b) {
            int d;
            if (a == null || b == null ||
                    (d = a.getClass().getName().
                            compareTo(b.getClass().getName())) == 0)
                d = (System.identityHashCode(a) <= System.identityHashCode(b) ?
                        -1 : 1);
            return d;
        }

        /**
         * Forms tree of the nodes linked from this node.
         * @return root of tree
         */
        final void treeify(HashMapAnalyze.Node<K,V>[] tab) {
            HashMapAnalyze.TreeNode<K,V> root = null;
            for (HashMapAnalyze.TreeNode<K,V> x = this, next; x != null; x = next) {
                next = (HashMapAnalyze.TreeNode<K,V>)x.next;
                x.left = x.right = null;
                if (root == null) {
                    x.parent = null;
                    x.red = false;
                    root = x;
                }
                else {
                    K k = x.key;
                    int h = x.hash;
                    Class<?> kc = null;
                    for (HashMapAnalyze.TreeNode<K,V> p = root;;) {
                        int dir, ph;
                        K pk = p.key;
                        if ((ph = p.hash) > h)
                            dir = -1;
                        else if (ph < h)
                            dir = 1;
                        else if ((kc == null &&
                                (kc = comparableClassFor(k)) == null) ||
                                (dir = compareComparables(kc, k, pk)) == 0)
                            dir = tieBreakOrder(k, pk);

                        HashMapAnalyze.TreeNode<K,V> xp = p;
                        if ((p = (dir <= 0) ? p.left : p.right) == null) {
                            x.parent = xp;
                            if (dir <= 0)
                                xp.left = x;
                            else
                                xp.right = x;
                            root = balanceInsertion(root, x);
                            break;
                        }
                    }
                }
            }
            moveRootToFront(tab, root);
        }

        /**
         * 将红黑树转换成一个list
         * @param map
         * @return
         */
        final HashMapAnalyze.Node<K,V> untreeify(HashMapAnalyze<K,V> map) {
            HashMapAnalyze.Node<K,V> hd = null, tl = null;
            for (HashMapAnalyze.Node<K,V> q = this; q != null; q = q.next) {
                HashMapAnalyze.Node<K,V> p = map.replacementNode(q, null);
                if (tl == null)
                    hd = p;
                else
                    tl.next = p;
                tl = p;
            }
            return hd;
        }

        /**
         * Tree version of putVal.
         */
        final HashMapAnalyze.TreeNode<K,V> putTreeVal(HashMapAnalyze<K,V> map, HashMapAnalyze.Node<K,V>[] tab,
                                               int h, K k, V v) {
            Class<?> kc = null;
            boolean searched = false;
            HashMapAnalyze.TreeNode<K,V> root = (parent != null) ? root() : this;
            for (HashMapAnalyze.TreeNode<K,V> p = root;;) {
                int dir, ph; K pk;
                if ((ph = p.hash) > h)
                    dir = -1;
                else if (ph < h)
                    dir = 1;
                else if ((pk = p.key) == k || (k != null && k.equals(pk)))
                    return p;
                else if ((kc == null &&
                        (kc = comparableClassFor(k)) == null) ||
                        (dir = compareComparables(kc, k, pk)) == 0) {
                    if (!searched) {
                        HashMapAnalyze.TreeNode<K,V> q, ch;
                        searched = true;
                        if (((ch = p.left) != null &&
                                (q = ch.find(h, k, kc)) != null) ||
                                ((ch = p.right) != null &&
                                        (q = ch.find(h, k, kc)) != null))
                            return q;
                    }
                    dir = tieBreakOrder(k, pk);
                }

                HashMapAnalyze.TreeNode<K,V> xp = p;
                if ((p = (dir <= 0) ? p.left : p.right) == null) {
                    HashMapAnalyze.Node<K,V> xpn = xp.next;
                    HashMapAnalyze.TreeNode<K,V> x = map.newTreeNode(h, k, v, xpn);
                    if (dir <= 0)
                        xp.left = x;
                    else
                        xp.right = x;
                    xp.next = x;
                    x.parent = x.prev = xp;
                    if (xpn != null)
                        ((HashMapAnalyze.TreeNode<K,V>)xpn).prev = x;
                    moveRootToFront(tab, balanceInsertion(root, x));
                    return null;
                }
            }
        }

        /**
         * Removes the given node, that must be present before this call.
         * This is messier than typical red-black deletion code because we
         * cannot swap the contents of an interior node with a leaf
         * successor that is pinned by "next" pointers that are accessible
         * independently during traversal. So instead we swap the tree
         * linkages. If the current tree appears to have too few nodes,
         * the bin is converted back to a plain bin. (The test triggers
         * somewhere between 2 and 6 nodes, depending on tree structure).
         */
        final void removeTreeNode(HashMapAnalyze<K,V> map, HashMapAnalyze.Node<K,V>[] tab,
                                  boolean movable) {
            int n;
            if (tab == null || (n = tab.length) == 0)
                return;
            int index = (n - 1) & hash;
            HashMapAnalyze.TreeNode<K,V> first = (HashMapAnalyze.TreeNode<K,V>)tab[index], root = first, rl;
            HashMapAnalyze.TreeNode<K,V> succ = (HashMapAnalyze.TreeNode<K,V>)next, pred = prev;
            if (pred == null)
                tab[index] = first = succ;
            else
                pred.next = succ;
            if (succ != null)
                succ.prev = pred;
            if (first == null)
                return;
            if (root.parent != null)
                root = root.root();
            if (root == null || root.right == null ||
                    (rl = root.left) == null || rl.left == null) {
                tab[index] = first.untreeify(map);  // too small
                return;
            }
            HashMapAnalyze.TreeNode<K,V> p = this, pl = left, pr = right, replacement;
            if (pl != null && pr != null) {
                HashMapAnalyze.TreeNode<K,V> s = pr, sl;
                while ((sl = s.left) != null) // find successor
                    s = sl;
                boolean c = s.red; s.red = p.red; p.red = c; // swap colors
                HashMapAnalyze.TreeNode<K,V> sr = s.right;
                HashMapAnalyze.TreeNode<K,V> pp = p.parent;
                if (s == pr) { // p was s's direct parent
                    p.parent = s;
                    s.right = p;
                }
                else {
                    HashMapAnalyze.TreeNode<K,V> sp = s.parent;
                    if ((p.parent = sp) != null) {
                        if (s == sp.left)
                            sp.left = p;
                        else
                            sp.right = p;
                    }
                    if ((s.right = pr) != null)
                        pr.parent = s;
                }
                p.left = null;
                if ((p.right = sr) != null)
                    sr.parent = p;
                if ((s.left = pl) != null)
                    pl.parent = s;
                if ((s.parent = pp) == null)
                    root = s;
                else if (p == pp.left)
                    pp.left = s;
                else
                    pp.right = s;
                if (sr != null)
                    replacement = sr;
                else
                    replacement = p;
            }
            else if (pl != null)
                replacement = pl;
            else if (pr != null)
                replacement = pr;
            else
                replacement = p;
            if (replacement != p) {
                HashMapAnalyze.TreeNode<K,V> pp = replacement.parent = p.parent;
                if (pp == null)
                    root = replacement;
                else if (p == pp.left)
                    pp.left = replacement;
                else
                    pp.right = replacement;
                p.left = p.right = p.parent = null;
            }

            HashMapAnalyze.TreeNode<K,V> r = p.red ? root : balanceDeletion(root, replacement);

            if (replacement == p) {  // detach
                HashMapAnalyze.TreeNode<K,V> pp = p.parent;
                p.parent = null;
                if (pp != null) {
                    if (p == pp.left)
                        pp.left = null;
                    else if (p == pp.right)
                        pp.right = null;
                }
            }
            if (movable)
                moveRootToFront(tab, r);
        }

        /**
         * Splits nodes in a tree bin into lower and upper tree bins,
         * or untreeifies if now too small. Called only from resize;
         * see above discussion about split bits and indices.
         *
         * @param map the map
         * @param tab the table for recording bin heads
         * @param index the index of the table being split
         * @param bit the bit of hash to split on
         */
        final void split(HashMapAnalyze<K,V> map, HashMapAnalyze.Node<K,V>[] tab, int index, int bit) {
            HashMapAnalyze.TreeNode<K,V> b = this;
            // Relink into lo and hi lists, preserving order
            HashMapAnalyze.TreeNode<K,V> loHead = null, loTail = null;
            HashMapAnalyze.TreeNode<K,V> hiHead = null, hiTail = null;
            int lc = 0, hc = 0;
            for (HashMapAnalyze.TreeNode<K,V> e = b, next; e != null; e = next) {
                next = (HashMapAnalyze.TreeNode<K,V>)e.next;
                e.next = null;

                if ((e.hash & bit) == 0) {
                    /**
                     * 表示这是低位，hash值小于oldCap
                     */
                    if ((e.prev = loTail) == null)
                        loHead = e;
                    else
                        loTail.next = e;
                    loTail = e;
                    ++lc;
                }
                else {
                    /**
                     * 表示这是高位，hash值大于等于oldCap
                     */
                    if ((e.prev = hiTail) == null)
                        hiHead = e;
                    else
                        hiTail.next = e;
                    hiTail = e;
                    ++hc;
                }
            }

            if (loHead != null) {
                if (lc <= UNTREEIFY_THRESHOLD)
                    tab[index] = loHead.untreeify(map);
                else {
                    tab[index] = loHead;
                    if (hiHead != null) // (else is already treeified)
                        loHead.treeify(tab);
                }
            }
            if (hiHead != null) {
                if (hc <= UNTREEIFY_THRESHOLD)
                    tab[index + bit] = hiHead.untreeify(map);
                else {
                    tab[index + bit] = hiHead;
                    if (loHead != null)
                        hiHead.treeify(tab);
                }
            }
        }

        /* ------------------------------------------------------------ */
        // Red-black tree methods, all adapted from CLR

        static <K,V> HashMapAnalyze.TreeNode<K,V> rotateLeft(HashMapAnalyze.TreeNode<K,V> root,
                                                      HashMapAnalyze.TreeNode<K,V> p) {
            HashMapAnalyze.TreeNode<K,V> r, pp, rl;
            if (p != null && (r = p.right) != null) {
                if ((rl = p.right = r.left) != null)
                    rl.parent = p;
                if ((pp = r.parent = p.parent) == null)
                    (root = r).red = false;
                else if (pp.left == p)
                    pp.left = r;
                else
                    pp.right = r;
                r.left = p;
                p.parent = r;
            }
            return root;
        }

        static <K,V> HashMapAnalyze.TreeNode<K,V> rotateRight(HashMapAnalyze.TreeNode<K,V> root,
                                                       HashMapAnalyze.TreeNode<K,V> p) {
            HashMapAnalyze.TreeNode<K,V> l, pp, lr;
            if (p != null && (l = p.left) != null) {
                if ((lr = p.left = l.right) != null)
                    lr.parent = p;
                if ((pp = l.parent = p.parent) == null)
                    (root = l).red = false;
                else if (pp.right == p)
                    pp.right = l;
                else
                    pp.left = l;
                l.right = p;
                p.parent = l;
            }
            return root;
        }

        static <K,V> HashMapAnalyze.TreeNode<K,V> balanceInsertion(HashMapAnalyze.TreeNode<K,V> root,
                                                            HashMapAnalyze.TreeNode<K,V> x) {
            x.red = true;
            for (HashMapAnalyze.TreeNode<K,V> xp, xpp, xppl, xppr;;) {
                if ((xp = x.parent) == null) {
                    x.red = false;
                    return x;
                }
                else if (!xp.red || (xpp = xp.parent) == null)
                    return root;
                if (xp == (xppl = xpp.left)) {
                    if ((xppr = xpp.right) != null && xppr.red) {
                        xppr.red = false;
                        xp.red = false;
                        xpp.red = true;
                        x = xpp;
                    }
                    else {
                        if (x == xp.right) {
                            root = rotateLeft(root, x = xp);
                            xpp = (xp = x.parent) == null ? null : xp.parent;
                        }
                        if (xp != null) {
                            xp.red = false;
                            if (xpp != null) {
                                xpp.red = true;
                                root = rotateRight(root, xpp);
                            }
                        }
                    }
                }
                else {
                    if (xppl != null && xppl.red) {
                        xppl.red = false;
                        xp.red = false;
                        xpp.red = true;
                        x = xpp;
                    }
                    else {
                        if (x == xp.left) {
                            root = rotateRight(root, x = xp);
                            xpp = (xp = x.parent) == null ? null : xp.parent;
                        }
                        if (xp != null) {
                            xp.red = false;
                            if (xpp != null) {
                                xpp.red = true;
                                root = rotateLeft(root, xpp);
                            }
                        }
                    }
                }
            }
        }

        static <K,V> HashMapAnalyze.TreeNode<K,V> balanceDeletion(HashMapAnalyze.TreeNode<K,V> root,
                                                           HashMapAnalyze.TreeNode<K,V> x) {
            for (HashMapAnalyze.TreeNode<K,V> xp, xpl, xpr;;)  {
                if (x == null || x == root)
                    return root;
                else if ((xp = x.parent) == null) {
                    x.red = false;
                    return x;
                }
                else if (x.red) {
                    x.red = false;
                    return root;
                }
                else if ((xpl = xp.left) == x) {
                    if ((xpr = xp.right) != null && xpr.red) {
                        xpr.red = false;
                        xp.red = true;
                        root = rotateLeft(root, xp);
                        xpr = (xp = x.parent) == null ? null : xp.right;
                    }
                    if (xpr == null)
                        x = xp;
                    else {
                        HashMapAnalyze.TreeNode<K,V> sl = xpr.left, sr = xpr.right;
                        if ((sr == null || !sr.red) &&
                                (sl == null || !sl.red)) {
                            xpr.red = true;
                            x = xp;
                        }
                        else {
                            if (sr == null || !sr.red) {
                                if (sl != null)
                                    sl.red = false;
                                xpr.red = true;
                                root = rotateRight(root, xpr);
                                xpr = (xp = x.parent) == null ?
                                        null : xp.right;
                            }
                            if (xpr != null) {
                                xpr.red = (xp == null) ? false : xp.red;
                                if ((sr = xpr.right) != null)
                                    sr.red = false;
                            }
                            if (xp != null) {
                                xp.red = false;
                                root = rotateLeft(root, xp);
                            }
                            x = root;
                        }
                    }
                }
                else { // symmetric
                    if (xpl != null && xpl.red) {
                        xpl.red = false;
                        xp.red = true;
                        root = rotateRight(root, xp);
                        xpl = (xp = x.parent) == null ? null : xp.left;
                    }
                    if (xpl == null)
                        x = xp;
                    else {
                        HashMapAnalyze.TreeNode<K,V> sl = xpl.left, sr = xpl.right;
                        if ((sl == null || !sl.red) &&
                                (sr == null || !sr.red)) {
                            xpl.red = true;
                            x = xp;
                        }
                        else {
                            if (sl == null || !sl.red) {
                                if (sr != null)
                                    sr.red = false;
                                xpl.red = true;
                                root = rotateLeft(root, xpl);
                                xpl = (xp = x.parent) == null ?
                                        null : xp.left;
                            }
                            if (xpl != null) {
                                xpl.red = (xp == null) ? false : xp.red;
                                if ((sl = xpl.left) != null)
                                    sl.red = false;
                            }
                            if (xp != null) {
                                xp.red = false;
                                root = rotateRight(root, xp);
                            }
                            x = root;
                        }
                    }
                }
            }
        }

        /**
         * Recursive invariant check
         */
        static <K,V> boolean checkInvariants(HashMapAnalyze.TreeNode<K,V> t) {
            HashMapAnalyze.TreeNode<K,V> tp = t.parent, tl = t.left, tr = t.right,
                    tb = t.prev, tn = (HashMapAnalyze.TreeNode<K,V>)t.next;
            if (tb != null && tb.next != t)
                return false;
            if (tn != null && tn.prev != t)
                return false;
            if (tp != null && t != tp.left && t != tp.right)
                return false;
            if (tl != null && (tl.parent != t || tl.hash > t.hash))
                return false;
            if (tr != null && (tr.parent != t || tr.hash < t.hash))
                return false;
            if (t.red && tl != null && tl.red && tr != null && tr.red)
                return false;
            if (tl != null && !checkInvariants(tl))
                return false;
            if (tr != null && !checkInvariants(tr))
                return false;
            return true;
        }
    }

    /**
     * 计算key的哈希值
     * @param key
     * @return
     */
    static final int hash(Object key) {
        int h;
        //为什么要无符号右移16位
        return (key == null) ? 0 : (h = key.hashCode()) ^ (h >>> 16);
    }

    public V put(K key, V value) {
        return putVal(hash(key), key, value, false, true);
    }

    final V putVal(int hash, K key, V value, boolean onlyIfAbsent,
                   boolean evict) {
        HashMapAnalyze.Node<K,V>[] tab;
        HashMapAnalyze.Node<K,V> p;
        int n, i;
        if ((tab = table) == null || (n = tab.length) == 0){
            //初始化table
            tab = resize();
            n = tab.length;
        }

        if ((p = tab[i = (n - 1) & hash]) == null)
            //如果当前index没有其他节点，则直接新建一个节点
            tab[i] = newNode(hash, key, value, null);
        else {
            //当前index已经有节点了，将节点插入一棵红黑树
            HashMapAnalyze.Node<K,V> e;
            K k;
            //注意：此时p表示红黑树的头结点
            if (p.hash == hash &&
                    ((k = p.key) == key || (key != null && key.equals(k))))
                //hash值相同且key值相同,表示是同一个key（有没可能有key值相同而hash不同的情况？）
                e = p;
            else if (p instanceof HashMapAnalyze.TreeNode)
                e = ((HashMapAnalyze.TreeNode<K,V>)p).putTreeVal(this, tab, hash, key, value);
            else {
                //这段有什么意义
                for (int binCount = 0; ; ++binCount) {
                    if ((e = p.next) == null) {
                        p.next = newNode(hash, key, value, null);
                        if (binCount >= TREEIFY_THRESHOLD - 1) // -1 for 1st
                            treeifyBin(tab, hash);
                        break;
                    }
                    if (e.hash == hash &&
                            ((k = e.key) == key || (key != null && key.equals(k))))
                        break;
                    p = e;
                }
            }
            if (e != null) { // existing mapping for key
                V oldValue = e.value;
                if (!onlyIfAbsent || oldValue == null)
                    e.value = value;
                afterNodeAccess(e);
                return oldValue;
            }
        }
        ++modCount;
        if (++size > threshold)
            resize();
        afterNodeInsertion(evict);
        return null;
    }


    /**
     * table空间的重新分配
     * @return
     */
    final HashMapAnalyze.Node<K,V>[] resize() {
        HashMapAnalyze.Node<K,V>[] oldTab = table;
        int oldCap = (oldTab == null) ? 0 : oldTab.length;
        int oldThr = threshold;
        int newCap, newThr = 0;

        if (oldCap > 0) {
            if (oldCap >= MAXIMUM_CAPACITY) {
                /**
                 * 容量超出最大值，直接将阈值设为最大（意图是不需要再为table扩容了）
                 */
                threshold = Integer.MAX_VALUE;
                return oldTab;
            }
            else if ((newCap = oldCap << 1) < MAXIMUM_CAPACITY &&
                    oldCap >= DEFAULT_INITIAL_CAPACITY)
            /**
             * 将容量扩大一倍，
             * 若：
             * 扩容前的容量 >= DEFAULT_INITIAL_CAPACITY
             * 扩容后的容量 < MAXIMUM_CAPACITY
             * 阈值也扩大一倍
             */
                newThr = oldThr << 1;
        }
        else if (oldThr > 0) // initial capacity was placed in threshold
        /**
         * 这种情况怎么会出现？
         * 当table容量为0，但是阈值不为0时：
         * table容量设置为阈值。
         * 意味着之后resize时容量与阈值将一直相等（因为会一起乘以2），直到容量超出最大范围。
         */
            newCap = oldThr;
        else {
            /**
             * 当容量与阈值均为0时，将进行初始化
             */
            newCap = DEFAULT_INITIAL_CAPACITY;
            newThr = (int)(DEFAULT_LOAD_FACTOR * DEFAULT_INITIAL_CAPACITY);
        }
        if (newThr == 0) {
            /**
             * 不知道这种情况什么时候出现
             */
            float ft = (float)newCap * loadFactor;
            newThr = (newCap < MAXIMUM_CAPACITY && ft < (float)MAXIMUM_CAPACITY ?
                    (int)ft : Integer.MAX_VALUE);
        }
        threshold = newThr;

        /**
         * 直接创建扩容数组
         */
        HashMapAnalyze.Node<K,V>[] newTab = (HashMapAnalyze.Node<K,V>[])new HashMapAnalyze.Node[newCap];
        table = newTab;
        if (oldTab != null) {
            for (int j = 0; j < oldCap; ++j) {
                HashMapAnalyze.Node<K,V> e;
                if ((e = oldTab[j]) != null) {
                    oldTab[j] = null;
                    if (e.next == null)
                        /**
                        * 如果这个桶只有一个元素，那么根据哈希值和扩容后的容量重新分配一个桶即可。
                        */
                        newTab[e.hash & (newCap - 1)] = e;
                    else if (e instanceof HashMapAnalyze.TreeNode)
                        ((HashMapAnalyze.TreeNode<K,V>)e).split(this, newTab, j, oldCap);
                    else { // preserve order
                        HashMapAnalyze.Node<K,V> loHead = null, loTail = null;
                        HashMapAnalyze.Node<K,V> hiHead = null, hiTail = null;
                        HashMapAnalyze.Node<K,V> next;
                        do {
                            next = e.next;
                            if ((e.hash & oldCap) == 0) {
                                if (loTail == null)
                                    loHead = e;
                                else
                                    loTail.next = e;
                                loTail = e;
                            }
                            else {
                                if (hiTail == null)
                                    hiHead = e;
                                else
                                    hiTail.next = e;
                                hiTail = e;
                            }
                        } while ((e = next) != null);
                        if (loTail != null) {
                            loTail.next = null;
                            newTab[j] = loHead;
                        }
                        if (hiTail != null) {
                            hiTail.next = null;
                            newTab[j + oldCap] = hiHead;
                        }
                    }
                }
            }
        }
        return newTab;
    }

    static Class<?> comparableClassFor(Object x) {
        if (x instanceof Comparable) {
            Class<?> c; Type[] ts, as; Type t; ParameterizedType p;
            if ((c = x.getClass()) == String.class) // bypass checks
                return c;
            if ((ts = c.getGenericInterfaces()) != null) {
                for (int i = 0; i < ts.length; ++i) {
                    if (((t = ts[i]) instanceof ParameterizedType) &&
                            ((p = (ParameterizedType)t).getRawType() ==
                                    Comparable.class) &&
                            (as = p.getActualTypeArguments()) != null &&
                            as.length == 1 && as[0] == c) // type arg is c
                        return c;
                }
            }
        }
        return null;
    }


    static int compareComparables(Class<?> kc, Object k, Object x) {
        return (x == null || x.getClass() != kc ? 0 :
                ((Comparable)k).compareTo(x));
    }

    /**
     * 替换一个node节点
     */
    HashMapAnalyze.Node<K,V> replacementNode(HashMapAnalyze.Node<K,V> p, HashMapAnalyze.Node<K,V> next) {
        return new HashMapAnalyze.Node<>(p.hash, p.key, p.value, next);
    }


    /**
     * 新建一个node节点
     */
    HashMapAnalyze.TreeNode<K,V> newTreeNode(int hash, K key, V value, HashMapAnalyze.Node<K,V> next) {
        return new HashMapAnalyze.TreeNode<>(hash, key, value, next);
    }


    @Override
    public Set<Entry<K, V>> entrySet() {
        Set<Map.Entry<K,V>> es;
        return (es = entrySet) == null ? (entrySet = new HashMapAnalyze.EntrySet()) : es;
    }

    HashMapAnalyze.Node<K,V> newNode(int hash, K key, V value, HashMapAnalyze.Node<K,V> next) {
        return new HashMapAnalyze.Node<>(hash, key, value, next);
    }

    HashMapAnalyze.TreeNode<K,V> replacementTreeNode(HashMapAnalyze.Node<K,V> p, HashMapAnalyze.Node<K,V> next) {
        return new HashMapAnalyze.TreeNode<>(p.hash, p.key, p.value, next);
    }



    void afterNodeAccess(HashMapAnalyze.Node<K,V> p) { }

    void afterNodeInsertion(boolean evict) { }

    final void treeifyBin(HashMapAnalyze.Node<K,V>[] tab, int hash) {
        int n, index; HashMapAnalyze.Node<K,V> e;
        if (tab == null || (n = tab.length) < MIN_TREEIFY_CAPACITY)
            resize();
        else if ((e = tab[index = (n - 1) & hash]) != null) {
            HashMapAnalyze.TreeNode<K,V> hd = null, tl = null;
            do {
                HashMapAnalyze.TreeNode<K,V> p = replacementTreeNode(e, null);
                if (tl == null)
                    hd = p;
                else {
                    p.prev = tl;
                    tl.next = p;
                }
                tl = p;
            } while ((e = e.next) != null);
            if ((tab[index] = hd) != null)
                hd.treeify(tab);
        }
    }


    final class EntrySet extends AbstractSet<Map.Entry<K,V>> {
        public final int size()                 { return size; }
        public final void clear()               { HashMapAnalyze.this.clear(); }
        public final Iterator<Map.Entry<K,V>> iterator() {
            return new HashMapAnalyze.EntryIterator();
        }
        public final boolean contains(Object o) {
            if (!(o instanceof Map.Entry))
                return false;
            Map.Entry<?,?> e = (Map.Entry<?,?>) o;
            Object key = e.getKey();
            HashMapAnalyze.Node<K,V> candidate = getNode(hash(key), key);
            return candidate != null && candidate.equals(e);
        }
        public final boolean remove(Object o) {
            if (o instanceof Map.Entry) {
                Map.Entry<?,?> e = (Map.Entry<?,?>) o;
                Object key = e.getKey();
                Object value = e.getValue();
                return removeNode(hash(key), key, value, true, true) != null;
            }
            return false;
        }
        public final Spliterator<Map.Entry<K,V>> spliterator() {
            return new HashMapAnalyze.EntrySpliterator<>(HashMapAnalyze.this, 0, -1, 0, 0);
        }
        public final void forEach(Consumer<? super Entry<K,V>> action) {
            HashMapAnalyze.Node<K,V>[] tab;
            if (action == null)
                throw new NullPointerException();
            if (size > 0 && (tab = table) != null) {
                int mc = modCount;
                for (int i = 0; i < tab.length; ++i) {
                    for (HashMapAnalyze.Node<K,V> e = tab[i]; e != null; e = e.next)
                        action.accept(e);
                }
                if (modCount != mc)
                    throw new ConcurrentModificationException();
            }
        }
    }
    abstract class HashIterator {
        HashMapAnalyze.Node<K,V> next;        // next entry to return
        HashMapAnalyze.Node<K,V> current;     // current entry
        int expectedModCount;  // for fast-fail
        int index;             // current slot

        HashIterator() {
            expectedModCount = modCount;
            HashMapAnalyze.Node<K,V>[] t = table;
            current = next = null;
            index = 0;
            if (t != null && size > 0) { // advance to first entry
                do {} while (index < t.length && (next = t[index++]) == null);
            }
        }

        public final boolean hasNext() {
            return next != null;
        }

        final HashMapAnalyze.Node<K,V> nextNode() {
            HashMapAnalyze.Node<K,V>[] t;
            HashMapAnalyze.Node<K,V> e = next;
            if (modCount != expectedModCount)
                throw new ConcurrentModificationException();
            if (e == null)
                throw new NoSuchElementException();
            if ((next = (current = e).next) == null && (t = table) != null) {
                do {} while (index < t.length && (next = t[index++]) == null);
            }
            return e;
        }

        public final void remove() {
            HashMapAnalyze.Node<K,V> p = current;
            if (p == null)
                throw new IllegalStateException();
            if (modCount != expectedModCount)
                throw new ConcurrentModificationException();
            current = null;
            K key = p.key;
            removeNode(hash(key), key, null, false, false);
            expectedModCount = modCount;
        }
    }

    final class EntryIterator extends HashMapAnalyze.HashIterator
            implements Iterator<Map.Entry<K,V>> {
        public final Map.Entry<K,V> next() { return nextNode(); }
    }


    final HashMapAnalyze.Node<K,V> removeNode(int hash, Object key, Object value,
                                       boolean matchValue, boolean movable) {
        HashMapAnalyze.Node<K,V>[] tab; HashMapAnalyze.Node<K,V> p; int n, index;
        if ((tab = table) != null && (n = tab.length) > 0 &&
                (p = tab[index = (n - 1) & hash]) != null) {
            HashMapAnalyze.Node<K,V> node = null, e; K k; V v;
            if (p.hash == hash &&
                    ((k = p.key) == key || (key != null && key.equals(k))))
                node = p;
            else if ((e = p.next) != null) {
                if (p instanceof HashMapAnalyze.TreeNode)
                    node = ((HashMapAnalyze.TreeNode<K,V>)p).getTreeNode(hash, key);
                else {
                    do {
                        if (e.hash == hash &&
                                ((k = e.key) == key ||
                                        (key != null && key.equals(k)))) {
                            node = e;
                            break;
                        }
                        p = e;
                    } while ((e = e.next) != null);
                }
            }
            if (node != null && (!matchValue || (v = node.value) == value ||
                    (value != null && value.equals(v)))) {
                if (node instanceof HashMapAnalyze.TreeNode)
                    ((HashMapAnalyze.TreeNode<K,V>)node).removeTreeNode(this, tab, movable);
                else if (node == p)
                    tab[index] = node.next;
                else
                    p.next = node.next;
                ++modCount;
                --size;
                afterNodeRemoval(node);
                return node;
            }
        }
        return null;
    }



    static class HashMapSpliterator<K,V> {
        final HashMapAnalyze<K,V> map;
        HashMapAnalyze.Node<K,V> current;          // current node
        int index;                  // current index, modified on advance/split
        int fence;                  // one past last index
        int est;                    // size estimate
        int expectedModCount;       // for comodification checks

        HashMapSpliterator(HashMapAnalyze<K,V> m, int origin,
                           int fence, int est,
                           int expectedModCount) {
            this.map = m;
            this.index = origin;
            this.fence = fence;
            this.est = est;
            this.expectedModCount = expectedModCount;
        }

        final int getFence() { // initialize fence and size on first use
            int hi;
            if ((hi = fence) < 0) {
                HashMapAnalyze<K,V> m = map;
                est = m.size;
                expectedModCount = m.modCount;
                HashMapAnalyze.Node<K,V>[] tab = m.table;
                hi = fence = (tab == null) ? 0 : tab.length;
            }
            return hi;
        }

        public final long estimateSize() {
            getFence(); // force init
            return (long) est;
        }
    }


    static final class EntrySpliterator<K,V>
            extends HashMapAnalyze.HashMapSpliterator<K,V>
            implements Spliterator<Map.Entry<K,V>> {
        EntrySpliterator(HashMapAnalyze<K,V> m, int origin, int fence, int est,
                         int expectedModCount) {
            super(m, origin, fence, est, expectedModCount);
        }

        public HashMapAnalyze.EntrySpliterator<K,V> trySplit() {
            int hi = getFence(), lo = index, mid = (lo + hi) >>> 1;
            return (lo >= mid || current != null) ? null :
                    new HashMapAnalyze.EntrySpliterator<>(map, lo, index = mid, est >>>= 1,
                            expectedModCount);
        }

        public void forEachRemaining(Consumer<? super Map.Entry<K,V>> action) {
            int i, hi, mc;
            if (action == null)
                throw new NullPointerException();
            HashMapAnalyze<K,V> m = map;
            HashMapAnalyze.Node<K,V>[] tab = m.table;
            if ((hi = fence) < 0) {
                mc = expectedModCount = m.modCount;
                hi = fence = (tab == null) ? 0 : tab.length;
            }
            else
                mc = expectedModCount;
            if (tab != null && tab.length >= hi &&
                    (i = index) >= 0 && (i < (index = hi) || current != null)) {
                HashMapAnalyze.Node<K,V> p = current;
                current = null;
                do {
                    if (p == null)
                        p = tab[i++];
                    else {
                        action.accept(p);
                        p = p.next;
                    }
                } while (p != null || i < hi);
                if (m.modCount != mc)
                    throw new ConcurrentModificationException();
            }
        }

        public boolean tryAdvance(Consumer<? super Map.Entry<K,V>> action) {
            int hi;
            if (action == null)
                throw new NullPointerException();
            HashMapAnalyze.Node<K,V>[] tab = map.table;
            if (tab != null && tab.length >= (hi = getFence()) && index >= 0) {
                while (current != null || index < hi) {
                    if (current == null)
                        current = tab[index++];
                    else {
                        HashMapAnalyze.Node<K,V> e = current;
                        current = current.next;
                        action.accept(e);
                        if (map.modCount != expectedModCount)
                            throw new ConcurrentModificationException();
                        return true;
                    }
                }
            }
            return false;
        }

        public int characteristics() {
            return (fence < 0 || est == map.size ? Spliterator.SIZED : 0) |
                    Spliterator.DISTINCT;
        }
    }

    final HashMapAnalyze.Node<K,V> getNode(int hash, Object key) {
        HashMapAnalyze.Node<K,V>[] tab;
        HashMapAnalyze.Node<K,V> first, e;
        int n;
        K k;
        if ((tab = table) != null && (n = tab.length) > 0 &&
                (first = tab[(n - 1) & hash]) != null) {
            if (first.hash == hash && // always check first node
                    ((k = first.key) == key || (key != null && key.equals(k))))
                return first;
            if ((e = first.next) != null) {
                if (first instanceof HashMapAnalyze.TreeNode)
                    return ((HashMapAnalyze.TreeNode<K,V>)first).getTreeNode(hash, key);
                do {
                    if (e.hash == hash &&
                            ((k = e.key) == key || (key != null && key.equals(k))))
                        return e;
                } while ((e = e.next) != null);
            }
        }
        return null;
    }


    void afterNodeRemoval(HashMapAnalyze.Node<K,V> p) { }

//    public static void main(String[] args) {
//        System.out.println(hash(17));
//    }
}
