def pmovsxbd1 : instruction :=
  definst "pmovsxbd" $ do
    pattern fun (v_2757 : reg (bv 128)) (v_2758 : reg (bv 128)) => do
      v_5459 <- getRegister v_2757;
      setRegister (lhs.of_reg v_2758) (concat (sext (extract v_5459 96 104) 32) (concat (sext (extract v_5459 104 112) 32) (concat (sext (extract v_5459 112 120) 32) (sext (extract v_5459 120 128) 32))));
      pure ()
    pat_end;
    pattern fun (v_2753 : Mem) (v_2754 : reg (bv 128)) => do
      v_12208 <- evaluateAddress v_2753;
      v_12209 <- load v_12208 4;
      setRegister (lhs.of_reg v_2754) (concat (sext (extract v_12209 0 8) 32) (concat (sext (extract v_12209 8 16) 32) (concat (sext (extract v_12209 16 24) 32) (sext (extract v_12209 24 32) 32))));
      pure ()
    pat_end
