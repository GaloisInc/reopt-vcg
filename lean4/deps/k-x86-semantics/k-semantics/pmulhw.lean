def pmulhw1 : instruction :=
  definst "pmulhw" $ do
    pattern fun (v_2864 : reg (bv 128)) (v_2865 : reg (bv 128)) => do
      v_5782 <- getRegister v_2865;
      v_5785 <- getRegister v_2864;
      setRegister (lhs.of_reg v_2865) (concat (extract (mul (sext (extract v_5782 0 16) 32) (sext (extract v_5785 0 16) 32)) 0 16) (concat (extract (mul (sext (extract v_5782 16 32) 32) (sext (extract v_5785 16 32) 32)) 0 16) (concat (extract (mul (sext (extract v_5782 32 48) 32) (sext (extract v_5785 32 48) 32)) 0 16) (concat (extract (mul (sext (extract v_5782 48 64) 32) (sext (extract v_5785 48 64) 32)) 0 16) (concat (extract (mul (sext (extract v_5782 64 80) 32) (sext (extract v_5785 64 80) 32)) 0 16) (concat (extract (mul (sext (extract v_5782 80 96) 32) (sext (extract v_5785 80 96) 32)) 0 16) (concat (extract (mul (sext (extract v_5782 96 112) 32) (sext (extract v_5785 96 112) 32)) 0 16) (extract (mul (sext (extract v_5782 112 128) 32) (sext (extract v_5785 112 128) 32)) 0 16))))))));
      pure ()
    pat_end;
    pattern fun (v_2861 : Mem) (v_2860 : reg (bv 128)) => do
      v_12537 <- getRegister v_2860;
      v_12540 <- evaluateAddress v_2861;
      v_12541 <- load v_12540 16;
      setRegister (lhs.of_reg v_2860) (concat (extract (mul (sext (extract v_12537 0 16) 32) (sext (extract v_12541 0 16) 32)) 0 16) (concat (extract (mul (sext (extract v_12537 16 32) 32) (sext (extract v_12541 16 32) 32)) 0 16) (concat (extract (mul (sext (extract v_12537 32 48) 32) (sext (extract v_12541 32 48) 32)) 0 16) (concat (extract (mul (sext (extract v_12537 48 64) 32) (sext (extract v_12541 48 64) 32)) 0 16) (concat (extract (mul (sext (extract v_12537 64 80) 32) (sext (extract v_12541 64 80) 32)) 0 16) (concat (extract (mul (sext (extract v_12537 80 96) 32) (sext (extract v_12541 80 96) 32)) 0 16) (concat (extract (mul (sext (extract v_12537 96 112) 32) (sext (extract v_12541 96 112) 32)) 0 16) (extract (mul (sext (extract v_12537 112 128) 32) (sext (extract v_12541 112 128) 32)) 0 16))))))));
      pure ()
    pat_end
