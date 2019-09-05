def movzbw1 : instruction :=
  definst "movzbw" $ do
    pattern fun (v_2745 : reg (bv 8)) (v_2747 : reg (bv 16)) => do
      v_4144 <- getRegister v_2745;
      setRegister (lhs.of_reg v_2747) (concat (expression.bv_nat 8 0) v_4144);
      pure ()
    pat_end;
    pattern fun (v_2736 : Mem) (v_2737 : reg (bv 16)) => do
      v_8746 <- evaluateAddress v_2736;
      v_8747 <- load v_8746 1;
      setRegister (lhs.of_reg v_2737) (concat (expression.bv_nat 8 0) v_8747);
      pure ()
    pat_end
