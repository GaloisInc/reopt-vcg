def vfmadd132sd1 : instruction :=
  definst "vfmadd132sd" $ do
    pattern fun (v_2527 : reg (bv 128)) (v_2528 : reg (bv 128)) (v_2529 : reg (bv 128)) => do
      v_4299 <- getRegister v_2529;
      v_4302 <- getRegister v_2528;
      v_4304 <- getRegister v_2527;
      setRegister (lhs.of_reg v_2529) (concat (extract v_4299 0 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4299 64 128) (extract v_4302 64 128) (extract v_4304 64 128)));
      pure ()
    pat_end;
    pattern fun (v_2521 : Mem) (v_2522 : reg (bv 128)) (v_2523 : reg (bv 128)) => do
      v_10317 <- getRegister v_2523;
      v_10320 <- getRegister v_2522;
      v_10322 <- evaluateAddress v_2521;
      v_10323 <- load v_10322 8;
      setRegister (lhs.of_reg v_2523) (concat (extract v_10317 0 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_10317 64 128) (extract v_10320 64 128) v_10323));
      pure ()
    pat_end
