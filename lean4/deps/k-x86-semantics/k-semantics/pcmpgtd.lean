def pcmpgtd1 : instruction :=
  definst "pcmpgtd" $ do
    pattern fun (v_2401 : reg (bv 128)) (v_2402 : reg (bv 128)) => do
      v_3941 <- getRegister v_2402;
      v_3943 <- getRegister v_2401;
      setRegister (lhs.of_reg v_2402) (concat (mux (sgt (extract v_3941 0 32) (extract v_3943 0 32)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_3941 32 64) (extract v_3943 32 64)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_3941 64 96) (extract v_3943 64 96)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (sgt (extract v_3941 96 128) (extract v_3943 96 128)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (v_2396 : Mem) (v_2397 : reg (bv 128)) => do
      v_11414 <- getRegister v_2397;
      v_11416 <- evaluateAddress v_2396;
      v_11417 <- load v_11416 16;
      setRegister (lhs.of_reg v_2397) (concat (mux (sgt (extract v_11414 0 32) (extract v_11417 0 32)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_11414 32 64) (extract v_11417 32 64)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_11414 64 96) (extract v_11417 64 96)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (sgt (extract v_11414 96 128) (extract v_11417 96 128)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end
