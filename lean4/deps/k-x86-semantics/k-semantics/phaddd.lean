def phaddd1 : instruction :=
  definst "phaddd" $ do
    pattern fun (v_2428 : reg (bv 128)) (v_2429 : reg (bv 128)) => do
      v_4029 <- getRegister v_2428;
      v_4037 <- getRegister v_2429;
      setRegister (lhs.of_reg v_2429) (concat (concat (concat (add (extract v_4029 0 32) (extract v_4029 32 64)) (add (extract v_4029 64 96) (extract v_4029 96 128))) (add (extract v_4037 0 32) (extract v_4037 32 64))) (add (extract v_4037 64 96) (extract v_4037 96 128)));
      pure ()
    pat_end;
    pattern fun (v_2423 : Mem) (v_2424 : reg (bv 128)) => do
      v_11493 <- evaluateAddress v_2423;
      v_11494 <- load v_11493 16;
      v_11502 <- getRegister v_2424;
      setRegister (lhs.of_reg v_2424) (concat (concat (concat (add (extract v_11494 0 32) (extract v_11494 32 64)) (add (extract v_11494 64 96) (extract v_11494 96 128))) (add (extract v_11502 0 32) (extract v_11502 32 64))) (add (extract v_11502 64 96) (extract v_11502 96 128)));
      pure ()
    pat_end
