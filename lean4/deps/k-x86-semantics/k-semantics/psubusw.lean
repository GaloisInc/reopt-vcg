def psubusw1 : instruction :=
  definst "psubusw" $ do
    pattern fun (v_3198 : reg (bv 128)) (v_3199 : reg (bv 128)) => do
      v_8510 <- getRegister v_3199;
      v_8513 <- getRegister v_3198;
      v_8516 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_8510 0 16)) (concat (expression.bv_nat 2 0) (extract v_8513 0 16)));
      v_8526 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_8510 16 32)) (concat (expression.bv_nat 2 0) (extract v_8513 16 32)));
      v_8536 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_8510 32 48)) (concat (expression.bv_nat 2 0) (extract v_8513 32 48)));
      v_8546 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_8510 48 64)) (concat (expression.bv_nat 2 0) (extract v_8513 48 64)));
      v_8556 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_8510 64 80)) (concat (expression.bv_nat 2 0) (extract v_8513 64 80)));
      v_8566 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_8510 80 96)) (concat (expression.bv_nat 2 0) (extract v_8513 80 96)));
      v_8576 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_8510 96 112)) (concat (expression.bv_nat 2 0) (extract v_8513 96 112)));
      v_8586 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_8510 112 128)) (concat (expression.bv_nat 2 0) (extract v_8513 112 128)));
      setRegister (lhs.of_reg v_3199) (concat (mux (sgt v_8516 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_8516 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_8516 2 18))) (concat (mux (sgt v_8526 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_8526 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_8526 2 18))) (concat (mux (sgt v_8536 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_8536 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_8536 2 18))) (concat (mux (sgt v_8546 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_8546 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_8546 2 18))) (concat (mux (sgt v_8556 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_8556 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_8556 2 18))) (concat (mux (sgt v_8566 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_8566 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_8566 2 18))) (concat (mux (sgt v_8576 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_8576 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_8576 2 18))) (mux (sgt v_8586 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_8586 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_8586 2 18))))))))));
      pure ()
    pat_end;
    pattern fun (v_3195 : Mem) (v_3194 : reg (bv 128)) => do
      v_14973 <- getRegister v_3194;
      v_14976 <- evaluateAddress v_3195;
      v_14977 <- load v_14976 16;
      v_14980 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_14973 0 16)) (concat (expression.bv_nat 2 0) (extract v_14977 0 16)));
      v_14990 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_14973 16 32)) (concat (expression.bv_nat 2 0) (extract v_14977 16 32)));
      v_15000 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_14973 32 48)) (concat (expression.bv_nat 2 0) (extract v_14977 32 48)));
      v_15010 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_14973 48 64)) (concat (expression.bv_nat 2 0) (extract v_14977 48 64)));
      v_15020 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_14973 64 80)) (concat (expression.bv_nat 2 0) (extract v_14977 64 80)));
      v_15030 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_14973 80 96)) (concat (expression.bv_nat 2 0) (extract v_14977 80 96)));
      v_15040 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_14973 96 112)) (concat (expression.bv_nat 2 0) (extract v_14977 96 112)));
      v_15050 <- eval (sub (concat (expression.bv_nat 2 0) (extract v_14973 112 128)) (concat (expression.bv_nat 2 0) (extract v_14977 112 128)));
      setRegister (lhs.of_reg v_3194) (concat (mux (sgt v_14980 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_14980 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_14980 2 18))) (concat (mux (sgt v_14990 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_14990 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_14990 2 18))) (concat (mux (sgt v_15000 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_15000 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_15000 2 18))) (concat (mux (sgt v_15010 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_15010 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_15010 2 18))) (concat (mux (sgt v_15020 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_15020 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_15020 2 18))) (concat (mux (sgt v_15030 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_15030 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_15030 2 18))) (concat (mux (sgt v_15040 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_15040 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_15040 2 18))) (mux (sgt v_15050 (expression.bv_nat 18 65535)) (expression.bv_nat 16 65535) (mux (slt v_15050 (expression.bv_nat 18 0)) (expression.bv_nat 16 0) (extract v_15050 2 18))))))))));
      pure ()
    pat_end
