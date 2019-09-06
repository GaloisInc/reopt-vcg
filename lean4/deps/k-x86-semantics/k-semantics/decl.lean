def decl1 : instruction :=
  definst "decl" $ do
    pattern fun (v_2776 : reg (bv 32)) => do
      v_4427 <- getRegister v_2776;
      v_4428 <- eval (sub v_4427 (expression.bv_nat 32 1));
      setRegister (lhs.of_reg v_2776) v_4428;
      setRegister af (eq (extract v_4427 28 32) (expression.bv_nat 4 0));
      setRegister of (bit_and (isBitSet v_4427 0) (eq (extract v_4427 1 32) (expression.bv_nat 31 0)));
      setRegister pf (parityFlag (extract v_4428 24 32));
      setRegister sf (isBitSet v_4428 0);
      setRegister zf (zeroFlag v_4428);
      pure ()
    pat_end;
    pattern fun (v_2773 : Mem) => do
      v_9086 <- evaluateAddress v_2773;
      v_9087 <- load v_9086 4;
      v_9088 <- eval (sub v_9087 (expression.bv_nat 32 1));
      store v_9086 v_9088 4;
      setRegister af (eq (extract v_9087 28 32) (expression.bv_nat 4 0));
      setRegister of (bit_and (isBitSet v_9087 0) (eq (extract v_9087 1 32) (expression.bv_nat 31 0)));
      setRegister pf (parityFlag (extract v_9088 24 32));
      setRegister sf (isBitSet v_9088 0);
      setRegister zf (zeroFlag v_9088);
      pure ()
    pat_end
