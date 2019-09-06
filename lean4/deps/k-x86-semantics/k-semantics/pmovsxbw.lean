def pmovsxbw1 : instruction :=
  definst "pmovsxbw" $ do
    pattern fun (v_2775 : reg (bv 128)) (v_2776 : reg (bv 128)) => do
      v_5487 <- getRegister v_2775;
      setRegister (lhs.of_reg v_2776) (concat (sext (extract v_5487 64 72) 16) (concat (sext (extract v_5487 72 80) 16) (concat (sext (extract v_5487 80 88) 16) (concat (sext (extract v_5487 88 96) 16) (concat (sext (extract v_5487 96 104) 16) (concat (sext (extract v_5487 104 112) 16) (concat (sext (extract v_5487 112 120) 16) (sext (extract v_5487 120 128) 16))))))));
      pure ()
    pat_end;
    pattern fun (v_2771 : Mem) (v_2772 : reg (bv 128)) => do
      v_12230 <- evaluateAddress v_2771;
      v_12231 <- load v_12230 8;
      setRegister (lhs.of_reg v_2772) (concat (sext (extract v_12231 0 8) 16) (concat (sext (extract v_12231 8 16) 16) (concat (sext (extract v_12231 16 24) 16) (concat (sext (extract v_12231 24 32) 16) (concat (sext (extract v_12231 32 40) 16) (concat (sext (extract v_12231 40 48) 16) (concat (sext (extract v_12231 48 56) 16) (sext (extract v_12231 56 64) 16))))))));
      pure ()
    pat_end
