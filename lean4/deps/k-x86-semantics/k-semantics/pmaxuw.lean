def pmaxuw1 : instruction :=
  definst "pmaxuw" $ do
    pattern fun (v_2593 : reg (bv 128)) (v_2594 : reg (bv 128)) => do
      v_5038 <- getRegister v_2594;
      v_5039 <- eval (extract v_5038 0 16);
      v_5040 <- getRegister v_2593;
      v_5041 <- eval (extract v_5040 0 16);
      v_5044 <- eval (extract v_5038 16 32);
      v_5045 <- eval (extract v_5040 16 32);
      v_5048 <- eval (extract v_5038 32 48);
      v_5049 <- eval (extract v_5040 32 48);
      v_5052 <- eval (extract v_5038 48 64);
      v_5053 <- eval (extract v_5040 48 64);
      v_5056 <- eval (extract v_5038 64 80);
      v_5057 <- eval (extract v_5040 64 80);
      v_5060 <- eval (extract v_5038 80 96);
      v_5061 <- eval (extract v_5040 80 96);
      v_5064 <- eval (extract v_5038 96 112);
      v_5065 <- eval (extract v_5040 96 112);
      v_5068 <- eval (extract v_5038 112 128);
      v_5069 <- eval (extract v_5040 112 128);
      setRegister (lhs.of_reg v_2594) (concat (mux (ugt v_5039 v_5041) v_5039 v_5041) (concat (mux (ugt v_5044 v_5045) v_5044 v_5045) (concat (mux (ugt v_5048 v_5049) v_5048 v_5049) (concat (mux (ugt v_5052 v_5053) v_5052 v_5053) (concat (mux (ugt v_5056 v_5057) v_5056 v_5057) (concat (mux (ugt v_5060 v_5061) v_5060 v_5061) (concat (mux (ugt v_5064 v_5065) v_5064 v_5065) (mux (ugt v_5068 v_5069) v_5068 v_5069))))))));
      pure ()
    pat_end;
    pattern fun (v_2588 : Mem) (v_2589 : reg (bv 128)) => do
      v_12426 <- getRegister v_2589;
      v_12427 <- eval (extract v_12426 0 16);
      v_12428 <- evaluateAddress v_2588;
      v_12429 <- load v_12428 16;
      v_12430 <- eval (extract v_12429 0 16);
      v_12433 <- eval (extract v_12426 16 32);
      v_12434 <- eval (extract v_12429 16 32);
      v_12437 <- eval (extract v_12426 32 48);
      v_12438 <- eval (extract v_12429 32 48);
      v_12441 <- eval (extract v_12426 48 64);
      v_12442 <- eval (extract v_12429 48 64);
      v_12445 <- eval (extract v_12426 64 80);
      v_12446 <- eval (extract v_12429 64 80);
      v_12449 <- eval (extract v_12426 80 96);
      v_12450 <- eval (extract v_12429 80 96);
      v_12453 <- eval (extract v_12426 96 112);
      v_12454 <- eval (extract v_12429 96 112);
      v_12457 <- eval (extract v_12426 112 128);
      v_12458 <- eval (extract v_12429 112 128);
      setRegister (lhs.of_reg v_2589) (concat (mux (ugt v_12427 v_12430) v_12427 v_12430) (concat (mux (ugt v_12433 v_12434) v_12433 v_12434) (concat (mux (ugt v_12437 v_12438) v_12437 v_12438) (concat (mux (ugt v_12441 v_12442) v_12441 v_12442) (concat (mux (ugt v_12445 v_12446) v_12445 v_12446) (concat (mux (ugt v_12449 v_12450) v_12449 v_12450) (concat (mux (ugt v_12453 v_12454) v_12453 v_12454) (mux (ugt v_12457 v_12458) v_12457 v_12458))))))));
      pure ()
    pat_end
