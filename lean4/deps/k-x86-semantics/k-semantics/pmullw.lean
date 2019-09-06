def pmullw1 : instruction :=
  definst "pmullw" $ do
    pattern fun (v_2910 : reg (bv 128)) (v_2911 : reg (bv 128)) => do
      v_5905 <- getRegister v_2911;
      v_5908 <- getRegister v_2910;
      setRegister (lhs.of_reg v_2911) (concat (extract (mul (sext (extract v_5905 0 16) 32) (sext (extract v_5908 0 16) 32)) 16 32) (concat (extract (mul (sext (extract v_5905 16 32) 32) (sext (extract v_5908 16 32) 32)) 16 32) (concat (extract (mul (sext (extract v_5905 32 48) 32) (sext (extract v_5908 32 48) 32)) 16 32) (concat (extract (mul (sext (extract v_5905 48 64) 32) (sext (extract v_5908 48 64) 32)) 16 32) (concat (extract (mul (sext (extract v_5905 64 80) 32) (sext (extract v_5908 64 80) 32)) 16 32) (concat (extract (mul (sext (extract v_5905 80 96) 32) (sext (extract v_5908 80 96) 32)) 16 32) (concat (extract (mul (sext (extract v_5905 96 112) 32) (sext (extract v_5908 96 112) 32)) 16 32) (extract (mul (sext (extract v_5905 112 128) 32) (sext (extract v_5908 112 128) 32)) 16 32))))))));
      pure ()
    pat_end;
    pattern fun (v_2906 : Mem) (v_2907 : reg (bv 128)) => do
      v_12603 <- getRegister v_2907;
      v_12606 <- evaluateAddress v_2906;
      v_12607 <- load v_12606 16;
      setRegister (lhs.of_reg v_2907) (concat (extract (mul (sext (extract v_12603 0 16) 32) (sext (extract v_12607 0 16) 32)) 16 32) (concat (extract (mul (sext (extract v_12603 16 32) 32) (sext (extract v_12607 16 32) 32)) 16 32) (concat (extract (mul (sext (extract v_12603 32 48) 32) (sext (extract v_12607 32 48) 32)) 16 32) (concat (extract (mul (sext (extract v_12603 48 64) 32) (sext (extract v_12607 48 64) 32)) 16 32) (concat (extract (mul (sext (extract v_12603 64 80) 32) (sext (extract v_12607 64 80) 32)) 16 32) (concat (extract (mul (sext (extract v_12603 80 96) 32) (sext (extract v_12607 80 96) 32)) 16 32) (concat (extract (mul (sext (extract v_12603 96 112) 32) (sext (extract v_12607 96 112) 32)) 16 32) (extract (mul (sext (extract v_12603 112 128) 32) (sext (extract v_12607 112 128) 32)) 16 32))))))));
      pure ()
    pat_end
