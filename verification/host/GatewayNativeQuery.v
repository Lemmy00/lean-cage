(* SPDX-License-Identifier: Apache-2.0 *)
(* §AR-host-boundary.primitives: Inspect the complete shared native operation and result types. *)
From HostGateway Require Import GatewayNativeImport.
Set Printing All.
Set Printing Depth 100000.
Redirect "native-operation-type" Print LeanCage_Host_NativeCode_Operation.
Redirect "native-product-type" Print LeanCage_Host_NativeCode_Product.
Redirect "native-reply-type" Print LeanCage_Host_NativeCode_Reply.
Redirect "native-references-type" Print LeanCage_Host_NativeCode_References.
Redirect "native-operation-axioms" Print Assumptions LeanCage_Host_NativeCode_Operation.
