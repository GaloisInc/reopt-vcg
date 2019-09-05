def pcmpeqd1 : instruction :=
  definst "pcmpeqd" $ do
    pattern fun (v_3322 : reg (bv 128)) (v_3323 : reg (bv 128)) => do
      v_6747 <- getRegister v_3323;
      v_6749 <- getRegister v_3322;
      setRegister (lhs.of_reg v_3323) (concat (mux (eq (extract v_6747 0 32) (extract v_6749 0 32)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_6747 32 64) (extract v_6749 32 64)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_6747 64 96) (extract v_6749 64 96)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (extract v_6747 96 128) (extract v_6749 96 128)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (v_3317 : Mem) (v_3318 : reg (bv 128)) => do
      v_10632 <- getRegister v_3318;
      v_10634 <- evaluateAddress v_3317;
      v_10635 <- load v_10634 16;
      setRegister (lhs.of_reg v_3318) (concat (mux (eq (extract v_10632 0 32) (extract v_10635 0 32)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_10632 32 64) (extract v_10635 32 64)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_10632 64 96) (extract v_10635 64 96)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (extract v_10632 96 128) (extract v_10635 96 128)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end
