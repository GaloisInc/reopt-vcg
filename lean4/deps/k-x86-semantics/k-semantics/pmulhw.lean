def pmulhw1 : instruction :=
  definst "pmulhw" $ do
    pattern fun (v_2892 : reg (bv 128)) (v_2893 : reg (bv 128)) => do
      v_5809 <- getRegister v_2893;
      v_5812 <- getRegister v_2892;
      setRegister (lhs.of_reg v_2893) (concat (extract (mul (sext (extract v_5809 0 16) 32) (sext (extract v_5812 0 16) 32)) 0 16) (concat (extract (mul (sext (extract v_5809 16 32) 32) (sext (extract v_5812 16 32) 32)) 0 16) (concat (extract (mul (sext (extract v_5809 32 48) 32) (sext (extract v_5812 32 48) 32)) 0 16) (concat (extract (mul (sext (extract v_5809 48 64) 32) (sext (extract v_5812 48 64) 32)) 0 16) (concat (extract (mul (sext (extract v_5809 64 80) 32) (sext (extract v_5812 64 80) 32)) 0 16) (concat (extract (mul (sext (extract v_5809 80 96) 32) (sext (extract v_5812 80 96) 32)) 0 16) (concat (extract (mul (sext (extract v_5809 96 112) 32) (sext (extract v_5812 96 112) 32)) 0 16) (extract (mul (sext (extract v_5809 112 128) 32) (sext (extract v_5812 112 128) 32)) 0 16))))))));
      pure ()
    pat_end;
    pattern fun (v_2888 : Mem) (v_2889 : reg (bv 128)) => do
      v_12513 <- getRegister v_2889;
      v_12516 <- evaluateAddress v_2888;
      v_12517 <- load v_12516 16;
      setRegister (lhs.of_reg v_2889) (concat (extract (mul (sext (extract v_12513 0 16) 32) (sext (extract v_12517 0 16) 32)) 0 16) (concat (extract (mul (sext (extract v_12513 16 32) 32) (sext (extract v_12517 16 32) 32)) 0 16) (concat (extract (mul (sext (extract v_12513 32 48) 32) (sext (extract v_12517 32 48) 32)) 0 16) (concat (extract (mul (sext (extract v_12513 48 64) 32) (sext (extract v_12517 48 64) 32)) 0 16) (concat (extract (mul (sext (extract v_12513 64 80) 32) (sext (extract v_12517 64 80) 32)) 0 16) (concat (extract (mul (sext (extract v_12513 80 96) 32) (sext (extract v_12517 80 96) 32)) 0 16) (concat (extract (mul (sext (extract v_12513 96 112) 32) (sext (extract v_12517 96 112) 32)) 0 16) (extract (mul (sext (extract v_12513 112 128) 32) (sext (extract v_12517 112 128) 32)) 0 16))))))));
      pure ()
    pat_end
