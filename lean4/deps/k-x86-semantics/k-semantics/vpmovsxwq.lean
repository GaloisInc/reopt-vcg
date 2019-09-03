def vpmovsxwq1 : instruction :=
  definst "vpmovsxwq" $ do
    pattern fun (v_2681 : reg (bv 128)) (v_2682 : reg (bv 128)) => do
      v_5694 <- getRegister v_2681;
      setRegister (lhs.of_reg v_2682) (concat (mi 64 (svalueMInt (extract v_5694 96 112))) (mi 64 (svalueMInt (extract v_5694 112 128))));
      pure ()
    pat_end;
    pattern fun (v_2690 : reg (bv 128)) (v_2691 : reg (bv 256)) => do
      v_5707 <- getRegister v_2690;
      setRegister (lhs.of_reg v_2691) (concat (mi 64 (svalueMInt (extract v_5707 64 80))) (concat (mi 64 (svalueMInt (extract v_5707 80 96))) (concat (mi 64 (svalueMInt (extract v_5707 96 112))) (mi 64 (svalueMInt (extract v_5707 112 128))))));
      pure ()
    pat_end;
    pattern fun (v_2678 : Mem) (v_2677 : reg (bv 128)) => do
      v_12842 <- evaluateAddress v_2678;
      v_12843 <- load v_12842 4;
      setRegister (lhs.of_reg v_2677) (concat (mi 64 (svalueMInt (extract v_12843 0 16))) (mi 64 (svalueMInt (extract v_12843 16 32))));
      pure ()
    pat_end;
    pattern fun (v_2686 : Mem) (v_2687 : reg (bv 256)) => do
      v_12852 <- evaluateAddress v_2686;
      v_12853 <- load v_12852 8;
      setRegister (lhs.of_reg v_2687) (concat (mi 64 (svalueMInt (extract v_12853 0 16))) (concat (mi 64 (svalueMInt (extract v_12853 16 32))) (concat (mi 64 (svalueMInt (extract v_12853 32 48))) (mi 64 (svalueMInt (extract v_12853 48 64))))));
      pure ()
    pat_end
