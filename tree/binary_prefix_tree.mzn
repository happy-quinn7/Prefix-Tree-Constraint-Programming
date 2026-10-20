int: n;          % number of inputs
int: radix;      % max number of children per op

string: name;

bool: commutative;

array[int] of int: arrival_list;        % arrival time of each input
array[int] of int: op_delay_list;       % delays for each of the operators (entry 1 is binary operator)
array[int] of int: op_cost_list;        % costs for each of the operators (entry 1 is binary operator)


%limits/deadlines, where -1 is no limit. required is the required time at root
int: required;
int: max_depth;
int: max_delay;
int: max_size;
int: max_cost;
int: max_ops_per_level;

set of int: LEAF = assert(n >= 2, "n must be >= 2", 0..n-1);     % assert is up here as its the first usage of n
set of int: OP = n..2*n-2;
set of int: NODE = 0..2*n-2;

int: NONE = 2*n-1;      %dummy parent of root and of unused operators

int: Tmax = assert(radix >= 2, "radix check", max(arrival_list) + (n - 1)*max(op_delay_list));  % upper bound of any arrival or finish time


% asserts for checking that the data is usable and correct, some declarations wrapped into the asserts
array[LEAF] of int: arrival =
  assert(length(arrival_list) = n, "arrival length check",
  array1d(LEAF, arrival_list));

array[int] of int: op_delay =
 assert(length(op_delay_list) = radix - 1, "op_delay length check",
 array1d(2..radix, op_delay_list));

array[int] of int: op_cost =
  assert(length(op_cost_list) = radix - 1, "op_cost length check",
  array1d(2..radix, op_cost_list));

constraint assert(forall(e in arrival_list)(e >= 0), "arrival_list elts >= 0");
constraint assert(forall(e in op_delay_list)(e >= 1), "op_delay_list elts >= 1");
constraint assert(forall(e in op_cost_list)(e >= 0), "op_cost_list elts >= 0");

constraint assert(required == -1 \/ required >= 1, "required limits");
constraint assert(max_depth == -1 \/ max_depth >= 1, "max_depth limits");
constraint assert(max_delay == -1 \/ max_delay >= 1, "max_delay limit");
constraint assert(max_size == -1 \/ max_size >= 1, "max_size limit");
constraint assert(max_cost == -1 \/ max_cost >= 1, "max_cost limit");
constraint assert(max_ops_per_level == -1 \/ max_ops_per_level >= 1, "max_ops_per_level limit");


% our two arrays that define the base behaviour of the tree, parent defining the parents of each NODE, and arity defining number of children, 0 = unused.
array[NODE] of var n..NONE: parent;
array[OP] of var 0..radix: arity;

array[NODE] of var 0..n: cnt; % where 0 means unused
array[NODE] of var 0..n-1: hi;
array[NODE] of var 0..n-1: lo;



% our basic predicates for defining the behaviour of the tree, familiar rules for the definition of a tree
predicate parent_larger() =
  forall(v in NODE)(parent[v] > v);
  
predicate leaf_has_parent() = 
  forall(v in LEAF)(parent[v] != NONE);
  
predicate arity_check() =
  forall(v in OP)(arity[v] != 1);
  
predicate arity_set() = 
  forall(v in OP)(count(u in NODE)((parent[u] = v)) = arity[v]);

predicate previous_has_to_be_used() = 
  forall(v in OP where v + 1 in OP)(arity[v+1] >= 2 -> arity[v] >= 2);

predicate unused_parent() =
  forall(v in OP)(arity[v] = 0 -> parent[v] = NONE);

predicate root_is_last_used() =
  forall(v in OP where v + 1 in OP)(arity[v] >= 2 ->
   (parent[v] = NONE <-> arity[v+1] = 0));
   
predicate unused_cnt_lo_hi_zero() = 
  forall(v in OP)(arity[v] = 0 -> (cnt[v] = 0 /\ lo[v] = 0 /\ hi[v] = 0));
  
predicate cnt_value() =
  forall(v in OP)(arity[v] >= 2 -> (sum(u in NODE)(bool2int(parent[u] = v) * cnt[u]) = cnt[v]));
 
predicate cnt_one_leaf() = 
  forall(v in LEAF)(cnt[v] = 1);
  
predicate hi_lo_leaf() = 
  forall(v in LEAF)(hi[v] = v /\ lo[v] = v);
  
predicate hi_at_least_childs_hi() = 
  forall(v in OP)(arity[v] >= 2 -> (forall(u in NODE)(parent[u] = v -> hi[v] >= hi[u])));
  
predicate hi_equals_child() = 
  forall(v in OP)(arity[v] >= 2 -> (exists(u in NODE)(parent[u] = v /\ hi[v] = hi[u])));
  
predicate lo_at_most_childs_lo() = 
  forall(v in OP)(arity[v] >= 2 -> (forall(u in NODE)(parent[u] = v -> lo[v] <= lo[u])));
  
predicate lo_equals_child() = 
  forall(v in OP)(arity[v] >= 2 -> (exists(u in NODE)(parent[u] = v /\ lo[v] = lo[u])));
  
predicate hi_ordering() = 
  forall(v in OP where v + 1 in OP)(arity[v+1] >= 2 -> hi[v] <= hi[v+1]);
  
   
constraint parent_larger();
constraint leaf_has_parent();
constraint arity_check();
constraint arity_set();
constraint previous_has_to_be_used();
constraint unused_parent();
constraint root_is_last_used();

constraint unused_cnt_lo_hi_zero();
constraint cnt_value();
constraint cnt_one_leaf();

constraint hi_lo_leaf();
constraint hi_at_least_childs_hi();
constraint hi_equals_child();
constraint lo_at_most_childs_lo();
constraint lo_equals_child();
constraint hi_ordering();

solve satisfy;


output["parent: \(parent)\narity: \(arity)\ncnt: \(cnt)\nhi: \(hi)\nlo: \(lo)\n"];