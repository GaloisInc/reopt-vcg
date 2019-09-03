def vfmadd132sd1 : instruction :=
  definst "vfmadd132sd" $ do
    pattern fun (v_2462 : reg (bv 128)) (v_2463 : reg (bv 128)) (v_2464 : reg (bv 128)) => do
      v_4239 <- getRegister v_2464;
      v_4242 <- getRegister v_2463;
      v_4244 <- getRegister v_2462;
      setRegister (lhs.of_reg v_2464) (concat (extract v_4239 0 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_4239 64 128) (extract v_4242 64 128) (extract v_4244 64 128)));
      pure ()
    pat_end;
    pattern fun (v_2459 : Mem) (v_2457 : reg (bv 128)) (v_2458 : reg (bv 128)) => do
      v_10240 <- getRegister v_2458;
      v_10243 <- getRegister v_2457;
      v_10245 <- evaluateAddress v_2459;
      v_10246 <- load v_10245 8;
      setRegister (lhs.of_reg v_2458) (concat (extract v_10240 0 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_10240 64 128) (extract v_10243 64 128) v_10246));
      pure ()
    pat_end
