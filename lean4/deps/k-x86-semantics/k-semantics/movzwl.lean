def movzwl1 : instruction :=
  definst "movzwl" $ do
    pattern fun (v_2704 : reg (bv 16)) (v_2705 : reg (bv 32)) => do
      v_4100 <- getRegister v_2704;
      setRegister (lhs.of_reg v_2705) (concat (expression.bv_nat 16 0) v_4100);
      pure ()
    pat_end;
    pattern fun (v_2700 : Mem) (v_2701 : reg (bv 32)) => do
      v_8886 <- evaluateAddress v_2700;
      v_8887 <- load v_8886 2;
      setRegister (lhs.of_reg v_2701) (concat (expression.bv_nat 16 0) v_8887);
      pure ()
    pat_end
