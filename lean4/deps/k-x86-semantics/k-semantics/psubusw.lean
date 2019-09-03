def psubusw1 : instruction :=
  definst "psubusw" $ do
    pattern fun (v_3149 : reg (bv 128)) (v_3150 : reg (bv 128)) => do
      v_8575 <- getRegister v_3150;
      v_8578 <- getRegister v_3149;
      v_8581 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_8575 0 16)) (concat (expression.bv_nat 2 0) (extract v_8578 0 16)));
      v_8591 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_8575 16 32)) (concat (expression.bv_nat 2 0) (extract v_8578 16 32)));
      v_8601 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_8575 32 48)) (concat (expression.bv_nat 2 0) (extract v_8578 32 48)));
      v_8611 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_8575 48 64)) (concat (expression.bv_nat 2 0) (extract v_8578 48 64)));
      v_8621 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_8575 64 80)) (concat (expression.bv_nat 2 0) (extract v_8578 64 80)));
      v_8631 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_8575 80 96)) (concat (expression.bv_nat 2 0) (extract v_8578 80 96)));
      v_8641 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_8575 96 112)) (concat (expression.bv_nat 2 0) (extract v_8578 96 112)));
      v_8651 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_8575 112 128)) (concat (expression.bv_nat 2 0) (extract v_8578 112 128)));
      setRegister (lhs.of_reg v_3150) (concat (mux (sgt v_8581 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_8581 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_8581 2 18))) (concat (mux (sgt v_8591 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_8591 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_8591 2 18))) (concat (mux (sgt v_8601 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_8601 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_8601 2 18))) (concat (mux (sgt v_8611 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_8611 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_8611 2 18))) (concat (mux (sgt v_8621 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_8621 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_8621 2 18))) (concat (mux (sgt v_8631 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_8631 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_8631 2 18))) (concat (mux (sgt v_8641 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_8641 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_8641 2 18))) (mux (sgt v_8651 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_8651 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_8651 2 18))))))))));
      pure ()
    pat_end;
    pattern fun (v_3145 : Mem) (v_3146 : reg (bv 128)) => do
      v_15175 <- getRegister v_3146;
      v_15178 <- evaluateAddress v_3145;
      v_15179 <- load v_15178 16;
      v_15182 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_15175 0 16)) (concat (expression.bv_nat 2 0) (extract v_15179 0 16)));
      v_15192 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_15175 16 32)) (concat (expression.bv_nat 2 0) (extract v_15179 16 32)));
      v_15202 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_15175 32 48)) (concat (expression.bv_nat 2 0) (extract v_15179 32 48)));
      v_15212 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_15175 48 64)) (concat (expression.bv_nat 2 0) (extract v_15179 48 64)));
      v_15222 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_15175 64 80)) (concat (expression.bv_nat 2 0) (extract v_15179 64 80)));
      v_15232 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_15175 80 96)) (concat (expression.bv_nat 2 0) (extract v_15179 80 96)));
      v_15242 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_15175 96 112)) (concat (expression.bv_nat 2 0) (extract v_15179 96 112)));
      v_15252 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_15175 112 128)) (concat (expression.bv_nat 2 0) (extract v_15179 112 128)));
      setRegister (lhs.of_reg v_3146) (concat (mux (sgt v_15182 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_15182 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_15182 2 18))) (concat (mux (sgt v_15192 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_15192 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_15192 2 18))) (concat (mux (sgt v_15202 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_15202 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_15202 2 18))) (concat (mux (sgt v_15212 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_15212 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_15212 2 18))) (concat (mux (sgt v_15222 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_15222 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_15222 2 18))) (concat (mux (sgt v_15232 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_15232 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_15232 2 18))) (concat (mux (sgt v_15242 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_15242 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_15242 2 18))) (mux (sgt v_15252 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_15252 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_15252 2 18))))))))));
      pure ()
    pat_end
