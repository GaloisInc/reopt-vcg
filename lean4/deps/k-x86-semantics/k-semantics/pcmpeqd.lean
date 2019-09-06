def pcmpeqd1 : instruction :=
  definst "pcmpeqd" $ do
    pattern fun (v_3347 : reg (bv 128)) (v_3348 : reg (bv 128)) => do
      v_6774 <- getRegister v_3348;
      v_6776 <- getRegister v_3347;
      setRegister (lhs.of_reg v_3348) (concat (mux (eq (extract v_6774 0 32) (extract v_6776 0 32)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_6774 32 64) (extract v_6776 32 64)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_6774 64 96) (extract v_6776 64 96)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (extract v_6774 96 128) (extract v_6776 96 128)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end;
    pattern fun (v_3343 : Mem) (v_3344 : reg (bv 128)) => do
      v_10659 <- getRegister v_3344;
      v_10661 <- evaluateAddress v_3343;
      v_10662 <- load v_10661 16;
      setRegister (lhs.of_reg v_3344) (concat (mux (eq (extract v_10659 0 32) (extract v_10662 0 32)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_10659 32 64) (extract v_10662 32 64)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (concat (mux (eq (extract v_10659 64 96) (extract v_10662 64 96)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)) (mux (eq (extract v_10659 96 128) (extract v_10662 96 128)) (expression.bv_nat 32 4294967295) (expression.bv_nat 32 0)))));
      pure ()
    pat_end
