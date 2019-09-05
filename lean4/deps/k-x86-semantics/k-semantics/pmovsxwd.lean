def pmovsxwd1 : instruction :=
  definst "pmovsxwd" $ do
    pattern fun (v_2765 : reg (bv 128)) (v_2766 : reg (bv 128)) => do
      v_5500 <- getRegister v_2765;
      setRegister (lhs.of_reg v_2766) (concat (sext (extract v_5500 64 80) 32) (concat (sext (extract v_5500 80 96) 32) (concat (sext (extract v_5500 96 112) 32) (sext (extract v_5500 112 128) 32))));
      pure ()
    pat_end;
    pattern fun (v_2762 : Mem) (v_2761 : reg (bv 128)) => do
      v_12288 <- evaluateAddress v_2762;
      v_12289 <- load v_12288 8;
      setRegister (lhs.of_reg v_2761) (concat (sext (extract v_12289 0 16) 32) (concat (sext (extract v_12289 16 32) 32) (concat (sext (extract v_12289 32 48) 32) (sext (extract v_12289 48 64) 32))));
      pure ()
    pat_end
