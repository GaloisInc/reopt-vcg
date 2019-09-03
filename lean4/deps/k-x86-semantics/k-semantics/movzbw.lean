def movzbw1 : instruction :=
  definst "movzbw" $ do
    pattern fun (v_2691 : reg (bv 8)) (v_2690 : reg (bv 16)) => do
      v_4090 <- getRegister v_2691;
      setRegister (lhs.of_reg v_2690) (concat (expression.bv_nat 8 0) v_4090);
      pure ()
    pat_end;
    pattern fun (v_2686 : Mem) (v_2687 : reg (bv 16)) => do
      v_8882 <- evaluateAddress v_2686;
      v_8883 <- load v_8882 1;
      setRegister (lhs.of_reg v_2687) (concat (expression.bv_nat 8 0) v_8883);
      pure ()
    pat_end
