def pmulhw1 : instruction :=
  definst "pmulhw" $ do
    pattern fun (v_2815 : reg (bv 128)) (v_2816 : reg (bv 128)) => do
      v_5751 <- getRegister v_2816;
      v_5754 <- getRegister v_2815;
      setRegister (lhs.of_reg v_2816) (concat (extract (mul (leanSignExtend (extract v_5751 0 16) 32) (leanSignExtend (extract v_5754 0 16) 32)) 0 16) (concat (extract (mul (leanSignExtend (extract v_5751 16 32) 32) (leanSignExtend (extract v_5754 16 32) 32)) 0 16) (concat (extract (mul (leanSignExtend (extract v_5751 32 48) 32) (leanSignExtend (extract v_5754 32 48) 32)) 0 16) (concat (extract (mul (leanSignExtend (extract v_5751 48 64) 32) (leanSignExtend (extract v_5754 48 64) 32)) 0 16) (concat (extract (mul (leanSignExtend (extract v_5751 64 80) 32) (leanSignExtend (extract v_5754 64 80) 32)) 0 16) (concat (extract (mul (leanSignExtend (extract v_5751 80 96) 32) (leanSignExtend (extract v_5754 80 96) 32)) 0 16) (concat (extract (mul (leanSignExtend (extract v_5751 96 112) 32) (leanSignExtend (extract v_5754 96 112) 32)) 0 16) (extract (mul (leanSignExtend (extract v_5751 112 128) 32) (leanSignExtend (extract v_5754 112 128) 32)) 0 16))))))));
      pure ()
    pat_end;
    pattern fun (v_2811 : Mem) (v_2812 : reg (bv 128)) => do
      v_12679 <- getRegister v_2812;
      v_12682 <- evaluateAddress v_2811;
      v_12683 <- load v_12682 16;
      setRegister (lhs.of_reg v_2812) (concat (extract (mul (leanSignExtend (extract v_12679 0 16) 32) (leanSignExtend (extract v_12683 0 16) 32)) 0 16) (concat (extract (mul (leanSignExtend (extract v_12679 16 32) 32) (leanSignExtend (extract v_12683 16 32) 32)) 0 16) (concat (extract (mul (leanSignExtend (extract v_12679 32 48) 32) (leanSignExtend (extract v_12683 32 48) 32)) 0 16) (concat (extract (mul (leanSignExtend (extract v_12679 48 64) 32) (leanSignExtend (extract v_12683 48 64) 32)) 0 16) (concat (extract (mul (leanSignExtend (extract v_12679 64 80) 32) (leanSignExtend (extract v_12683 64 80) 32)) 0 16) (concat (extract (mul (leanSignExtend (extract v_12679 80 96) 32) (leanSignExtend (extract v_12683 80 96) 32)) 0 16) (concat (extract (mul (leanSignExtend (extract v_12679 96 112) 32) (leanSignExtend (extract v_12683 96 112) 32)) 0 16) (extract (mul (leanSignExtend (extract v_12679 112 128) 32) (leanSignExtend (extract v_12683 112 128) 32)) 0 16))))))));
      pure ()
    pat_end
