def vpmovsxwd1 : instruction :=
  definst "vpmovsxwd" $ do
    pattern fun (v_2755 : reg (bv 128)) (v_2756 : reg (bv 128)) => do
      v_5679 <- getRegister v_2755;
      setRegister (lhs.of_reg v_2756) (concat (sext (extract v_5679 64 80) 32) (concat (sext (extract v_5679 80 96) 32) (concat (sext (extract v_5679 96 112) 32) (sext (extract v_5679 112 128) 32))));
      pure ()
    pat_end;
    pattern fun (v_2765 : reg (bv 128)) (v_2764 : reg (bv 256)) => do
      v_5696 <- getRegister v_2765;
      setRegister (lhs.of_reg v_2764) (concat (sext (extract v_5696 0 16) 32) (concat (sext (extract v_5696 16 32) 32) (concat (sext (extract v_5696 32 48) 32) (concat (sext (extract v_5696 48 64) 32) (concat (sext (extract v_5696 64 80) 32) (concat (sext (extract v_5696 80 96) 32) (concat (sext (extract v_5696 96 112) 32) (sext (extract v_5696 112 128) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_2750 : Mem) (v_2751 : reg (bv 128)) => do
      v_12086 <- evaluateAddress v_2750;
      v_12087 <- load v_12086 8;
      setRegister (lhs.of_reg v_2751) (concat (sext (extract v_12087 0 16) 32) (concat (sext (extract v_12087 16 32) 32) (concat (sext (extract v_12087 32 48) 32) (sext (extract v_12087 48 64) 32))));
      pure ()
    pat_end;
    pattern fun (v_2759 : Mem) (v_2760 : reg (bv 256)) => do
      v_12100 <- evaluateAddress v_2759;
      v_12101 <- load v_12100 16;
      setRegister (lhs.of_reg v_2760) (concat (sext (extract v_12101 0 16) 32) (concat (sext (extract v_12101 16 32) 32) (concat (sext (extract v_12101 32 48) 32) (concat (sext (extract v_12101 48 64) 32) (concat (sext (extract v_12101 64 80) 32) (concat (sext (extract v_12101 80 96) 32) (concat (sext (extract v_12101 96 112) 32) (sext (extract v_12101 112 128) 32))))))));
      pure ()
    pat_end
