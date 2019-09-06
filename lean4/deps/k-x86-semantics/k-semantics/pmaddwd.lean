def pmaddwd1 : instruction :=
  definst "pmaddwd" $ do
    pattern fun (v_2630 : reg (bv 128)) (v_2631 : reg (bv 128)) => do
      v_4705 <- getRegister v_2630;
      v_4708 <- getRegister v_2631;
      setRegister (lhs.of_reg v_2631) (concat (add (mul (sext (extract v_4705 16 32) 32) (sext (extract v_4708 16 32) 32)) (mul (sext (extract v_4705 0 16) 32) (sext (extract v_4708 0 16) 32))) (concat (add (mul (sext (extract v_4705 48 64) 32) (sext (extract v_4708 48 64) 32)) (mul (sext (extract v_4705 32 48) 32) (sext (extract v_4708 32 48) 32))) (concat (add (mul (sext (extract v_4705 80 96) 32) (sext (extract v_4708 80 96) 32)) (mul (sext (extract v_4705 64 80) 32) (sext (extract v_4708 64 80) 32))) (add (mul (sext (extract v_4705 112 128) 32) (sext (extract v_4708 112 128) 32)) (mul (sext (extract v_4705 96 112) 32) (sext (extract v_4708 96 112) 32))))));
      pure ()
    pat_end;
    pattern fun (v_2626 : Mem) (v_2627 : reg (bv 128)) => do
      v_11561 <- evaluateAddress v_2626;
      v_11562 <- load v_11561 16;
      v_11565 <- getRegister v_2627;
      setRegister (lhs.of_reg v_2627) (concat (add (mul (sext (extract v_11562 16 32) 32) (sext (extract v_11565 16 32) 32)) (mul (sext (extract v_11562 0 16) 32) (sext (extract v_11565 0 16) 32))) (concat (add (mul (sext (extract v_11562 48 64) 32) (sext (extract v_11565 48 64) 32)) (mul (sext (extract v_11562 32 48) 32) (sext (extract v_11565 32 48) 32))) (concat (add (mul (sext (extract v_11562 80 96) 32) (sext (extract v_11565 80 96) 32)) (mul (sext (extract v_11562 64 80) 32) (sext (extract v_11565 64 80) 32))) (add (mul (sext (extract v_11562 112 128) 32) (sext (extract v_11565 112 128) 32)) (mul (sext (extract v_11562 96 112) 32) (sext (extract v_11565 96 112) 32))))));
      pure ()
    pat_end
