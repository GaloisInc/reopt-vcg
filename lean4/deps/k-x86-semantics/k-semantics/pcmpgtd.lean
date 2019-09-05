def pcmpgtd1 : instruction :=
  definst "pcmpgtd" $ do
    pattern fun (v_2464 : reg (bv 128)) (v_2465 : reg (bv 128)) => do
      v_4005 <- getRegister v_2465;
      v_4007 <- getRegister v_2464;
      setRegister (lhs.of_reg v_2465) (concat (mux (sgt (extract v_4005 0 32) (extract v_4007 0 32)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_4005 32 64) (extract v_4007 32 64)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_4005 64 96) (extract v_4007 64 96)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (sgt (extract v_4005 96 128) (extract v_4007 96 128)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (v_2461 : Mem) (v_2460 : reg (bv 128)) => do
      v_10974 <- getRegister v_2460;
      v_10976 <- evaluateAddress v_2461;
      v_10977 <- load v_10976 16;
      setRegister (lhs.of_reg v_2460) (concat (mux (sgt (extract v_10974 0 32) (extract v_10977 0 32)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_10974 32 64) (extract v_10977 32 64)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_10974 64 96) (extract v_10977 64 96)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (sgt (extract v_10974 96 128) (extract v_10977 96 128)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end
