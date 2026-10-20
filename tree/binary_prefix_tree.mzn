int: n;
int: radix;

string: name;

bool: commutative;

array[int] of int: arrival_list;
array[int] of int: op_delay_list;
array[int] of int: op_cost_list;

int: required;
int: max_depth;
int: max_delay;
int: max_size;
int: max_cost;
int: max_ops_per_level;

set of int: LEAF = assert(n >= 2, "n must be >= 2", 0..n-1);     % up here as its the first usage of n
set of int: OP = n..2*n-2;
set of int: NODE = 0..2*n-2;

int: NONE = 2*n-1;
int: Tmax = assert(radix >= 2, "radix check", max(arrival_list) + (n - 1)*max(op_delay_list));

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


output[
  "n = \(n)\n",
  "radix = \(radix)\n",
  "commutative = \(commutative)\n",
  "arrival = \(arrival)\n",
  "op_delay = \(op_delay)\n",
  "op_cost = \(op_cost)\n",
  "required = \(required)\n",
  "max_depth = \(max_depth)\n",
  "max_delay = \(max_delay)\n",
  "max_size = \(max_size)\n",
  "max_cost = \(max_cost)\n",
  "max_ops_per_level = \(max_ops_per_level)\n"
  ];