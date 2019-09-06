def pcmpgtd1 : instruction :=
  definst "pcmpgtd" $ do
    pattern fun (v_2492 : reg (bv 128)) (v_2493 : reg (bv 128)) => do
      v_4032 <- getRegister v_2493;
      v_4034 <- getRegister v_2492;
      setRegister (lhs.of_reg v_2493) (concat (mux (sgt (extract v_4032 0 32) (extract v_4034 0 32)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_4032 32 64) (extract v_4034 32 64)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_4032 64 96) (extract v_4034 64 96)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (sgt (extract v_4032 96 128) (extract v_4034 96 128)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (v_2488 : Mem) (v_2489 : reg (bv 128)) => do
      v_10950 <- getRegister v_2489;
      v_10952 <- evaluateAddress v_2488;
      v_10953 <- load v_10952 16;
      setRegister (lhs.of_reg v_2489) (concat (mux (sgt (extract v_10950 0 32) (extract v_10953 0 32)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_10950 32 64) (extract v_10953 32 64)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (sgt (extract v_10950 64 96) (extract v_10953 64 96)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (sgt (extract v_10950 96 128) (extract v_10953 96 128)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end
