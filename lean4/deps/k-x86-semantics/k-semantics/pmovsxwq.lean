def pmovsxwq1 : instruction :=
  definst "pmovsxwq" $ do
    pattern fun (v_2711 : reg (bv 128)) (v_2712 : reg (bv 128)) => do
      v_5573 <- getRegister v_2711;
      setRegister (lhs.of_reg v_2712) (concat (mi 64 (svalueMInt (extract v_5573 96 112))) (mi 64 (svalueMInt (extract v_5573 112 128))));
      pure ()
    pat_end;
    pattern fun (v_2706 : Mem) (v_2707 : reg (bv 128)) => do
      v_12857 <- evaluateAddress v_2706;
      v_12858 <- load v_12857 4;
      setRegister (lhs.of_reg v_2707) (concat (mi 64 (svalueMInt (extract v_12858 0 16))) (mi 64 (svalueMInt (extract v_12858 16 32))));
      pure ()
    pat_end
