def pmullw1 : instruction :=
  definst "pmullw" $ do
    pattern fun (v_2882 : reg (bv 128)) (v_2883 : reg (bv 128)) => do
      v_5878 <- getRegister v_2883;
      v_5881 <- getRegister v_2882;
      setRegister (lhs.of_reg v_2883) (concat (extract (mul (sext (extract v_5878 0 16) 32) (sext (extract v_5881 0 16) 32)) 16 32) (concat (extract (mul (sext (extract v_5878 16 32) 32) (sext (extract v_5881 16 32) 32)) 16 32) (concat (extract (mul (sext (extract v_5878 32 48) 32) (sext (extract v_5881 32 48) 32)) 16 32) (concat (extract (mul (sext (extract v_5878 48 64) 32) (sext (extract v_5881 48 64) 32)) 16 32) (concat (extract (mul (sext (extract v_5878 64 80) 32) (sext (extract v_5881 64 80) 32)) 16 32) (concat (extract (mul (sext (extract v_5878 80 96) 32) (sext (extract v_5881 80 96) 32)) 16 32) (concat (extract (mul (sext (extract v_5878 96 112) 32) (sext (extract v_5881 96 112) 32)) 16 32) (extract (mul (sext (extract v_5878 112 128) 32) (sext (extract v_5881 112 128) 32)) 16 32))))))));
      pure ()
    pat_end;
    pattern fun (v_2879 : Mem) (v_2878 : reg (bv 128)) => do
      v_12627 <- getRegister v_2878;
      v_12630 <- evaluateAddress v_2879;
      v_12631 <- load v_12630 16;
      setRegister (lhs.of_reg v_2878) (concat (extract (mul (sext (extract v_12627 0 16) 32) (sext (extract v_12631 0 16) 32)) 16 32) (concat (extract (mul (sext (extract v_12627 16 32) 32) (sext (extract v_12631 16 32) 32)) 16 32) (concat (extract (mul (sext (extract v_12627 32 48) 32) (sext (extract v_12631 32 48) 32)) 16 32) (concat (extract (mul (sext (extract v_12627 48 64) 32) (sext (extract v_12631 48 64) 32)) 16 32) (concat (extract (mul (sext (extract v_12627 64 80) 32) (sext (extract v_12631 64 80) 32)) 16 32) (concat (extract (mul (sext (extract v_12627 80 96) 32) (sext (extract v_12631 80 96) 32)) 16 32) (concat (extract (mul (sext (extract v_12627 96 112) 32) (sext (extract v_12631 96 112) 32)) 16 32) (extract (mul (sext (extract v_12627 112 128) 32) (sext (extract v_12631 112 128) 32)) 16 32))))))));
      pure ()
    pat_end
