def pmullw1 : instruction :=
  definst "pmullw" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_1;
      v_3 <- evaluateAddress mem_0;
      v_4 <- load v_3 16;
      setRegister (lhs.of_reg xmm_1) (concat (extract (mul (sext (extract v_2 0 16) 32) (sext (extract v_4 0 16) 32)) 16 32) (concat (extract (mul (sext (extract v_2 16 32) 32) (sext (extract v_4 16 32) 32)) 16 32) (concat (extract (mul (sext (extract v_2 32 48) 32) (sext (extract v_4 32 48) 32)) 16 32) (concat (extract (mul (sext (extract v_2 48 64) 32) (sext (extract v_4 48 64) 32)) 16 32) (concat (extract (mul (sext (extract v_2 64 80) 32) (sext (extract v_4 64 80) 32)) 16 32) (concat (extract (mul (sext (extract v_2 80 96) 32) (sext (extract v_4 80 96) 32)) 16 32) (concat (extract (mul (sext (extract v_2 96 112) 32) (sext (extract v_4 96 112) 32)) 16 32) (extract (mul (sext (extract v_2 112 128) 32) (sext (extract v_4 112 128) 32)) 16 32))))))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) => do
      v_2 <- getRegister xmm_1;
      v_3 <- getRegister xmm_0;
      setRegister (lhs.of_reg xmm_1) (concat (extract (mul (sext (extract v_2 0 16) 32) (sext (extract v_3 0 16) 32)) 16 32) (concat (extract (mul (sext (extract v_2 16 32) 32) (sext (extract v_3 16 32) 32)) 16 32) (concat (extract (mul (sext (extract v_2 32 48) 32) (sext (extract v_3 32 48) 32)) 16 32) (concat (extract (mul (sext (extract v_2 48 64) 32) (sext (extract v_3 48 64) 32)) 16 32) (concat (extract (mul (sext (extract v_2 64 80) 32) (sext (extract v_3 64 80) 32)) 16 32) (concat (extract (mul (sext (extract v_2 80 96) 32) (sext (extract v_3 80 96) 32)) 16 32) (concat (extract (mul (sext (extract v_2 96 112) 32) (sext (extract v_3 96 112) 32)) 16 32) (extract (mul (sext (extract v_2 112 128) 32) (sext (extract v_3 112 128) 32)) 16 32))))))));
      pure ()
    pat_end
