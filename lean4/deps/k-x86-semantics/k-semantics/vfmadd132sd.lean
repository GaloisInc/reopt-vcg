def vfmadd132sd1 : instruction :=
  definst "vfmadd132sd" $ do
    pattern fun (v_2475 : reg (bv 128)) (v_2476 : reg (bv 128)) (v_2477 : reg (bv 128)) => do
      v_4503 <- getRegister v_2477;
      v_4506 <- getRegister v_2476;
      v_4508 <- getRegister v_2475;
      setRegister (lhs.of_reg v_2477) (concat (extract v_4503 0 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4503 64 128) (extract v_4506 64 128) (extract v_4508 64 128)));
      pure ()
    pat_end;
    pattern fun (v_2472 : Mem) (v_2470 : reg (bv 128)) (v_2471 : reg (bv 128)) => do
      v_15436 <- getRegister v_2471;
      v_15439 <- getRegister v_2470;
      v_15441 <- evaluateAddress v_2472;
      v_15442 <- load v_15441 8;
      setRegister (lhs.of_reg v_2471) (concat (extract v_15436 0 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_15436 64 128) (extract v_15439 64 128) v_15442));
      pure ()
    pat_end
