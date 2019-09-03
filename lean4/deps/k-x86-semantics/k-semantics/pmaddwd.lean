def pmaddwd1 : instruction :=
  definst "pmaddwd" $ do
    pattern fun (v_2553 : reg (bv 128)) (v_2554 : reg (bv 128)) => do
      v_4647 <- getRegister v_2553;
      v_4650 <- getRegister v_2554;
      setRegister (lhs.of_reg v_2554) (concat (add (mul (leanSignExtend (extract v_4647 16 32) 32) (leanSignExtend (extract v_4650 16 32) 32)) (mul (leanSignExtend (extract v_4647 0 16) 32) (leanSignExtend (extract v_4650 0 16) 32))) (concat (add (mul (leanSignExtend (extract v_4647 48 64) 32) (leanSignExtend (extract v_4650 48 64) 32)) (mul (leanSignExtend (extract v_4647 32 48) 32) (leanSignExtend (extract v_4650 32 48) 32))) (concat (add (mul (leanSignExtend (extract v_4647 80 96) 32) (leanSignExtend (extract v_4650 80 96) 32)) (mul (leanSignExtend (extract v_4647 64 80) 32) (leanSignExtend (extract v_4650 64 80) 32))) (add (mul (leanSignExtend (extract v_4647 112 128) 32) (leanSignExtend (extract v_4650 112 128) 32)) (mul (leanSignExtend (extract v_4647 96 112) 32) (leanSignExtend (extract v_4650 96 112) 32))))));
      pure ()
    pat_end;
    pattern fun (v_2549 : Mem) (v_2550 : reg (bv 128)) => do
      v_11727 <- evaluateAddress v_2549;
      v_11728 <- load v_11727 16;
      v_11731 <- getRegister v_2550;
      setRegister (lhs.of_reg v_2550) (concat (add (mul (leanSignExtend (extract v_11728 16 32) 32) (leanSignExtend (extract v_11731 16 32) 32)) (mul (leanSignExtend (extract v_11728 0 16) 32) (leanSignExtend (extract v_11731 0 16) 32))) (concat (add (mul (leanSignExtend (extract v_11728 48 64) 32) (leanSignExtend (extract v_11731 48 64) 32)) (mul (leanSignExtend (extract v_11728 32 48) 32) (leanSignExtend (extract v_11731 32 48) 32))) (concat (add (mul (leanSignExtend (extract v_11728 80 96) 32) (leanSignExtend (extract v_11731 80 96) 32)) (mul (leanSignExtend (extract v_11728 64 80) 32) (leanSignExtend (extract v_11731 64 80) 32))) (add (mul (leanSignExtend (extract v_11728 112 128) 32) (leanSignExtend (extract v_11731 112 128) 32)) (mul (leanSignExtend (extract v_11728 96 112) 32) (leanSignExtend (extract v_11731 96 112) 32))))));
      pure ()
    pat_end
