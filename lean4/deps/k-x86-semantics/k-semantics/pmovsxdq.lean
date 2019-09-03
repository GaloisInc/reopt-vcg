def pmovsxdq1 : instruction :=
  definst "pmovsxdq" $ do
    pattern fun (v_2693 : reg (bv 128)) (v_2694 : reg (bv 128)) => do
      v_5539 <- getRegister v_2693;
      setRegister (lhs.of_reg v_2694) (concat (mi 64 (svalueMInt (extract v_5539 64 96))) (mi 64 (svalueMInt (extract v_5539 96 128))));
      pure ()
    pat_end;
    pattern fun (v_2688 : Mem) (v_2689 : reg (bv 128)) => do
      v_12829 <- evaluateAddress v_2688;
      v_12830 <- load v_12829 8;
      setRegister (lhs.of_reg v_2689) (concat (mi 64 (svalueMInt (extract v_12830 0 32))) (mi 64 (svalueMInt (extract v_12830 32 64))));
      pure ()
    pat_end
