def pmaxud1 : instruction :=
  definst "pmaxud" $ do
    pattern fun (v_2584 : reg (bv 128)) (v_2585 : reg (bv 128)) => do
      v_5012 <- getRegister v_2585;
      v_5013 <- eval (extract v_5012 0 32);
      v_5014 <- getRegister v_2584;
      v_5015 <- eval (extract v_5014 0 32);
      v_5018 <- eval (extract v_5012 32 64);
      v_5019 <- eval (extract v_5014 32 64);
      v_5022 <- eval (extract v_5012 64 96);
      v_5023 <- eval (extract v_5014 64 96);
      v_5026 <- eval (extract v_5012 96 128);
      v_5027 <- eval (extract v_5014 96 128);
      setRegister (lhs.of_reg v_2585) (concat (mux (ugt v_5013 v_5015) v_5013 v_5015) (concat (mux (ugt v_5018 v_5019) v_5018 v_5019) (concat (mux (ugt v_5022 v_5023) v_5022 v_5023) (mux (ugt v_5026 v_5027) v_5026 v_5027))));
      pure ()
    pat_end;
    pattern fun (v_2579 : Mem) (v_2580 : reg (bv 128)) => do
      v_12403 <- getRegister v_2580;
      v_12404 <- eval (extract v_12403 0 32);
      v_12405 <- evaluateAddress v_2579;
      v_12406 <- load v_12405 16;
      v_12407 <- eval (extract v_12406 0 32);
      v_12410 <- eval (extract v_12403 32 64);
      v_12411 <- eval (extract v_12406 32 64);
      v_12414 <- eval (extract v_12403 64 96);
      v_12415 <- eval (extract v_12406 64 96);
      v_12418 <- eval (extract v_12403 96 128);
      v_12419 <- eval (extract v_12406 96 128);
      setRegister (lhs.of_reg v_2580) (concat (mux (ugt v_12404 v_12407) v_12404 v_12407) (concat (mux (ugt v_12410 v_12411) v_12410 v_12411) (concat (mux (ugt v_12414 v_12415) v_12414 v_12415) (mux (ugt v_12418 v_12419) v_12418 v_12419))));
      pure ()
    pat_end
