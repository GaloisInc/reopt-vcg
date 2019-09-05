def pmovsxbd1 : instruction :=
  definst "pmovsxbd" $ do
    pattern fun (v_2729 : reg (bv 128)) (v_2730 : reg (bv 128)) => do
      v_5432 <- getRegister v_2729;
      setRegister (lhs.of_reg v_2730) (concat (sext (extract v_5432 96 104) 32) (concat (sext (extract v_5432 104 112) 32) (concat (sext (extract v_5432 112 120) 32) (sext (extract v_5432 120 128) 32))));
      pure ()
    pat_end;
    pattern fun (v_2726 : Mem) (v_2725 : reg (bv 128)) => do
      v_12232 <- evaluateAddress v_2726;
      v_12233 <- load v_12232 4;
      setRegister (lhs.of_reg v_2725) (concat (sext (extract v_12233 0 8) 32) (concat (sext (extract v_12233 8 16) 32) (concat (sext (extract v_12233 16 24) 32) (sext (extract v_12233 24 32) 32))));
      pure ()
    pat_end
