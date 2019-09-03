def pcmpgtd1 : instruction :=
  definst "pcmpgtd" $ do
    pattern fun (v_2415 : reg (bv 128)) (v_2416 : reg (bv 128)) => do
      v_3954 <- getRegister v_2416;
      v_3956 <- getRegister v_2415;
      setRegister (lhs.of_reg v_2416) (concat (mux (sgt (extract v_3954 0 32) (extract v_3956 0 32)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_3954 32 64) (extract v_3956 32 64)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_3954 64 96) (extract v_3956 64 96)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (sgt (extract v_3954 96 128) (extract v_3956 96 128)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (v_2411 : Mem) (v_2412 : reg (bv 128)) => do
      v_11097 <- getRegister v_2412;
      v_11099 <- evaluateAddress v_2411;
      v_11100 <- load v_11099 16;
      setRegister (lhs.of_reg v_2412) (concat (mux (sgt (extract v_11097 0 32) (extract v_11100 0 32)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_11097 32 64) (extract v_11100 32 64)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_11097 64 96) (extract v_11100 64 96)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (sgt (extract v_11097 96 128) (extract v_11100 96 128)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end
