def btrq1 : instruction :=
  definst "btrq" $ do
    pattern fun (v_3217 : imm int) (v_3220 : reg (bv 64)) => do
      v_6045 <- getRegister v_3220;
      v_6048 <- eval (sext (bv_and (handleImmediateWithSignExtend v_3217 8 8) (expression.bv_nat 8 63)) 64);
      setRegister (lhs.of_reg v_3220) (bv_and v_6045 (bv_xor (extract (shl (expression.bv_nat 64 1) v_6048) 0 64) (expression.bv_nat 64 18446744073709551615)));
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_6045 v_6048) 63);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3224 : reg (bv 64)) (v_3225 : reg (bv 64)) => do
      v_6061 <- getRegister v_3225;
      v_6062 <- getRegister v_3224;
      v_6063 <- eval (bv_and v_6062 (expression.bv_nat 64 63));
      setRegister (lhs.of_reg v_3225) (bv_and v_6061 (bv_xor (extract (shl (expression.bv_nat 64 1) v_6063) 0 64) (expression.bv_nat 64 18446744073709551615)));
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_6061 v_6063) 63);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3209 : imm int) (v_3212 : Mem) => do
      v_10628 <- evaluateAddress v_3212;
      v_10629 <- eval (handleImmediateWithSignExtend v_3209 8 8);
      v_10633 <- eval (add v_10628 (concat (expression.bv_nat 59 0) (bv_and (extract v_10629 0 5) (expression.bv_nat 5 7))));
      v_10634 <- load v_10633 1;
      v_10637 <- eval (concat (expression.bv_nat 5 0) (bv_and (extract v_10629 5 8) (expression.bv_nat 3 7)));
      store v_10633 (bv_and v_10634 (bv_xor (extract (shl (expression.bv_nat 8 1) v_10637) 0 8) (expression.bv_nat 8 255))) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_10634 v_10637) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end;
    pattern fun (v_3216 : reg (bv 64)) (v_3215 : Mem) => do
      v_10650 <- evaluateAddress v_3215;
      v_10651 <- getRegister v_3216;
      v_10654 <- eval (add v_10650 (concat (expression.bv_nat 3 0) (extract v_10651 0 61)));
      v_10655 <- load v_10654 1;
      v_10657 <- eval (concat (expression.bv_nat 5 0) (extract v_10651 61 64));
      store v_10654 (bv_and v_10655 (bv_xor (extract (shl (expression.bv_nat 8 1) v_10657) 0 8) (expression.bv_nat 8 255))) 1;
      setRegister af undef;
      setRegister cf (isBitSet (lshr v_10655 v_10657) 7);
      setRegister of undef;
      setRegister pf undef;
      setRegister sf undef;
      pure ()
    pat_end
