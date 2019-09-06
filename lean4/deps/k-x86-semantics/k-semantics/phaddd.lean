def phaddd1 : instruction :=
  definst "phaddd" $ do
    pattern fun (v_2519 : reg (bv 128)) (v_2520 : reg (bv 128)) => do
      v_4120 <- getRegister v_2519;
      v_4128 <- getRegister v_2520;
      setRegister (lhs.of_reg v_2520) (concat (concat (concat (add (extract v_4120 0 32) (extract v_4120 32 64)) (add (extract v_4120 64 96) (extract v_4120 96 128))) (add (extract v_4128 0 32) (extract v_4128 32 64))) (add (extract v_4128 64 96) (extract v_4128 96 128)));
      pure ()
    pat_end;
    pattern fun (v_2515 : Mem) (v_2516 : reg (bv 128)) => do
      v_11029 <- evaluateAddress v_2515;
      v_11030 <- load v_11029 16;
      v_11038 <- getRegister v_2516;
      setRegister (lhs.of_reg v_2516) (concat (concat (concat (add (extract v_11030 0 32) (extract v_11030 32 64)) (add (extract v_11030 64 96) (extract v_11030 96 128))) (add (extract v_11038 0 32) (extract v_11038 32 64))) (add (extract v_11038 64 96) (extract v_11038 96 128)));
      pure ()
    pat_end
