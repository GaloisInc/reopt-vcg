def vfmadd132sd1 : instruction :=
  definst "vfmadd132sd" $ do
    pattern fun (v_2551 : reg (bv 128)) (v_2552 : reg (bv 128)) (v_2553 : reg (bv 128)) => do
      v_4326 <- getRegister v_2553;
      v_4329 <- getRegister v_2552;
      v_4331 <- getRegister v_2551;
      setRegister (lhs.of_reg v_2553) (concat (extract v_4326 0 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4326 64 128) (extract v_4329 64 128) (extract v_4331 64 128)));
      pure ()
    pat_end;
    pattern fun (v_2548 : Mem) (v_2546 : reg (bv 128)) (v_2547 : reg (bv 128)) => do
      v_10344 <- getRegister v_2547;
      v_10347 <- getRegister v_2546;
      v_10349 <- evaluateAddress v_2548;
      v_10350 <- load v_10349 8;
      setRegister (lhs.of_reg v_2547) (concat (extract v_10344 0 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_10344 64 128) (extract v_10347 64 128) v_10350));
      pure ()
    pat_end
