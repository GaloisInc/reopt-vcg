def decw1 : instruction :=
  definst "decw" $ do
    pattern fun (v_2790 : reg (bv 16)) => do
      v_4469 <- getRegister v_2790;
      v_4470 <- eval (sub v_4469 (expression.bv_nat 16 1));
      setRegister (lhs.of_reg v_2790) v_4470;
      setRegister af (eq (extract v_4469 12 16) (expression.bv_nat 4 0));
      setRegister of (bit_and (isBitSet v_4469 0) (eq (extract v_4469 1 16) (expression.bv_nat 15 0)));
      setRegister pf (parityFlag (extract v_4470 8 16));
      setRegister sf (isBitSet v_4470 0);
      setRegister zf (zeroFlag v_4470);
      pure ()
    pat_end;
    pattern fun (v_2787 : Mem) => do
      v_9124 <- evaluateAddress v_2787;
      v_9125 <- load v_9124 2;
      v_9126 <- eval (sub v_9125 (expression.bv_nat 16 1));
      store v_9124 v_9126 2;
      setRegister af (eq (extract v_9125 12 16) (expression.bv_nat 4 0));
      setRegister of (bit_and (isBitSet v_9125 0) (eq (extract v_9125 1 16) (expression.bv_nat 15 0)));
      setRegister pf (parityFlag (extract v_9126 8 16));
      setRegister sf (isBitSet v_9126 0);
      setRegister zf (zeroFlag v_9126);
      pure ()
    pat_end
