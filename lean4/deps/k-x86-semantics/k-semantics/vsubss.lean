def vsubss1 : instruction :=
  definst "vsubss" $ do
    pattern fun (v_2418 : reg (bv 128)) (v_2419 : reg (bv 128)) (v_2420 : reg (bv 128)) => do
      v_3373 <- getRegister v_2419;
      v_3377 <- getRegister v_2418;
      setRegister (lhs.of_reg v_2420) (concat (extract v_3373 0 96) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_3373 96 128) 24 8) (MInt2Float (extract v_3377 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2411 : Mem) (v_2413 : reg (bv 128)) (v_2414 : reg (bv 128)) => do
      v_6649 <- getRegister v_2413;
      v_6653 <- evaluateAddress v_2411;
      v_6654 <- load v_6653 4;
      setRegister (lhs.of_reg v_2414) (concat (extract v_6649 0 96) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_6649 96 128) 24 8) (MInt2Float v_6654 24 8)) 32));
      pure ()
    pat_end
