def movzwl1 : instruction :=
  definst "movzwl" $ do
    pattern fun (v_2780 : reg (bv 16)) (v_2781 : reg (bv 32)) => do
      v_4178 <- getRegister v_2780;
      setRegister (lhs.of_reg v_2781) (concat (expression.bv_nat 16 0) v_4178);
      pure ()
    pat_end;
    pattern fun (v_2776 : Mem) (v_2777 : reg (bv 32)) => do
      v_8777 <- evaluateAddress v_2776;
      v_8778 <- load v_8777 2;
      setRegister (lhs.of_reg v_2777) (concat (expression.bv_nat 16 0) v_8778);
      pure ()
    pat_end
