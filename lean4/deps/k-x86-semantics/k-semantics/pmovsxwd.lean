def pmovsxwd1 : instruction :=
  definst "pmovsxwd" $ do
    pattern fun (v_2793 : reg (bv 128)) (v_2794 : reg (bv 128)) => do
      v_5527 <- getRegister v_2793;
      setRegister (lhs.of_reg v_2794) (concat (sext (extract v_5527 64 80) 32) (concat (sext (extract v_5527 80 96) 32) (concat (sext (extract v_5527 96 112) 32) (sext (extract v_5527 112 128) 32))));
      pure ()
    pat_end;
    pattern fun (v_2789 : Mem) (v_2790 : reg (bv 128)) => do
      v_12264 <- evaluateAddress v_2789;
      v_12265 <- load v_12264 8;
      setRegister (lhs.of_reg v_2790) (concat (sext (extract v_12265 0 16) 32) (concat (sext (extract v_12265 16 32) 32) (concat (sext (extract v_12265 32 48) 32) (sext (extract v_12265 48 64) 32))));
      pure ()
    pat_end
