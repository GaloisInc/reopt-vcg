def vptest1 : instruction :=
  definst "vptest" $ do
    pattern fun (v_2561 : reg (bv 128)) (v_2562 : reg (bv 128)) => do
      v_6114 <- getRegister v_2562;
      v_6118 <- getRegister v_2561;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (expression.bv_nat 1 0);
      setRegister af (expression.bv_nat 1 0);
      setRegister zf (zeroFlag (bv_and v_6114 v_6118));
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (mux (eq (bv_and (bv_xor v_6114 (mi (bitwidthMInt v_6114) -1)) v_6118) (expression.bv_nat 128 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2569 : reg (bv 256)) (v_2570 : reg (bv 256)) => do
      v_6134 <- getRegister v_2570;
      v_6138 <- getRegister v_2569;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (expression.bv_nat 1 0);
      setRegister af (expression.bv_nat 1 0);
      setRegister zf (zeroFlag (bv_and v_6134 v_6138));
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (mux (eq (bv_and (bv_xor v_6134 (mi (bitwidthMInt v_6134) -1)) v_6138) (expression.bv_nat 256 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2556 : Mem) (v_2557 : reg (bv 128)) => do
      v_12452 <- getRegister v_2557;
      v_12456 <- evaluateAddress v_2556;
      v_12457 <- load v_12456 16;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (expression.bv_nat 1 0);
      setRegister af (expression.bv_nat 1 0);
      setRegister zf (zeroFlag (bv_and v_12452 v_12457));
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (mux (eq (bv_and (bv_xor v_12452 (mi (bitwidthMInt v_12452) -1)) v_12457) (expression.bv_nat 128 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_2565 : Mem) (v_2566 : reg (bv 256)) => do
      v_12469 <- getRegister v_2566;
      v_12473 <- evaluateAddress v_2565;
      v_12474 <- load v_12473 32;
      setRegister of (expression.bv_nat 1 0);
      setRegister pf (expression.bv_nat 1 0);
      setRegister af (expression.bv_nat 1 0);
      setRegister zf (zeroFlag (bv_and v_12469 v_12474));
      setRegister sf (expression.bv_nat 1 0);
      setRegister cf (mux (eq (bv_and (bv_xor v_12469 (mi (bitwidthMInt v_12469) -1)) v_12474) (expression.bv_nat 256 0)) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
