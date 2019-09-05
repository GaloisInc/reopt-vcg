def pmulld1 : instruction :=
  definst "pmulld" $ do
    pattern fun (v_2873 : reg (bv 128)) (v_2874 : reg (bv 128)) => do
      v_5844 <- getRegister v_2874;
      v_5847 <- getRegister v_2873;
      setRegister (lhs.of_reg v_2874) (concat (extract (mul (sext (extract v_5844 0 32) 64) (sext (extract v_5847 0 32) 64)) 32 64) (concat (extract (mul (sext (extract v_5844 32 64) 64) (sext (extract v_5847 32 64) 64)) 32 64) (concat (extract (mul (sext (extract v_5844 64 96) 64) (sext (extract v_5847 64 96) 64)) 32 64) (extract (mul (sext (extract v_5844 96 128) 64) (sext (extract v_5847 96 128) 64)) 32 64))));
      pure ()
    pat_end;
    pattern fun (v_2870 : Mem) (v_2869 : reg (bv 128)) => do
      v_12596 <- getRegister v_2869;
      v_12599 <- evaluateAddress v_2870;
      v_12600 <- load v_12599 16;
      setRegister (lhs.of_reg v_2869) (concat (extract (mul (sext (extract v_12596 0 32) 64) (sext (extract v_12600 0 32) 64)) 32 64) (concat (extract (mul (sext (extract v_12596 32 64) 64) (sext (extract v_12600 32 64) 64)) 32 64) (concat (extract (mul (sext (extract v_12596 64 96) 64) (sext (extract v_12600 64 96) 64)) 32 64) (extract (mul (sext (extract v_12596 96 128) 64) (sext (extract v_12600 96 128) 64)) 32 64))));
      pure ()
    pat_end
