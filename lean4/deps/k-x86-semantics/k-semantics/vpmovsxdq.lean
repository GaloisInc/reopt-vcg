def vpmovsxdq1 : instruction :=
  definst "vpmovsxdq" $ do
    pattern fun (v_2645 : reg (bv 128)) (v_2646 : reg (bv 128)) => do
      v_5602 <- getRegister v_2645;
      setRegister (lhs.of_reg v_2646) (concat (mi 64 (svalueMInt (extract v_5602 64 96))) (mi 64 (svalueMInt (extract v_5602 96 128))));
      pure ()
    pat_end;
    pattern fun (v_2654 : reg (bv 128)) (v_2655 : reg (bv 256)) => do
      v_5615 <- getRegister v_2654;
      setRegister (lhs.of_reg v_2655) (concat (mi 64 (svalueMInt (extract v_5615 0 32))) (concat (mi 64 (svalueMInt (extract v_5615 32 64))) (concat (mi 64 (svalueMInt (extract v_5615 64 96))) (mi 64 (svalueMInt (extract v_5615 96 128))))));
      pure ()
    pat_end;
    pattern fun (v_2642 : Mem) (v_2641 : reg (bv 128)) => do
      v_12762 <- evaluateAddress v_2642;
      v_12763 <- load v_12762 8;
      setRegister (lhs.of_reg v_2641) (concat (mi 64 (svalueMInt (extract v_12763 0 32))) (mi 64 (svalueMInt (extract v_12763 32 64))));
      pure ()
    pat_end;
    pattern fun (v_2650 : Mem) (v_2651 : reg (bv 256)) => do
      v_12772 <- evaluateAddress v_2650;
      v_12773 <- load v_12772 16;
      setRegister (lhs.of_reg v_2651) (concat (mi 64 (svalueMInt (extract v_12773 0 32))) (concat (mi 64 (svalueMInt (extract v_12773 32 64))) (concat (mi 64 (svalueMInt (extract v_12773 64 96))) (mi 64 (svalueMInt (extract v_12773 96 128))))));
      pure ()
    pat_end
