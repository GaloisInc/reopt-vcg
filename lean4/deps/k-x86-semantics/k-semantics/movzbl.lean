def movzbl1 : instruction :=
  definst "movzbl" $ do
    pattern fun (v_2748 : reg (bv 8)) (v_2749 : reg (bv 32)) => do
      v_4154 <- getRegister v_2748;
      setRegister (lhs.of_reg v_2749) (concat (expression.bv_nat 24 0) v_4154);
      pure ()
    pat_end;
    pattern fun (v_2739 : Mem) (v_2740 : reg (bv 32)) => do
      v_8765 <- evaluateAddress v_2739;
      v_8766 <- load v_8765 1;
      setRegister (lhs.of_reg v_2740) (concat (expression.bv_nat 24 0) v_8766);
      pure ()
    pat_end
