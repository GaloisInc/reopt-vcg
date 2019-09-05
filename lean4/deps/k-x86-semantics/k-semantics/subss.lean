def subss1 : instruction :=
  definst "subss" $ do
    pattern fun (v_3295 : reg (bv 128)) (v_3296 : reg (bv 128)) => do
      v_6633 <- getRegister v_3296;
      v_6637 <- getRegister v_3295;
      setRegister (lhs.of_reg v_3296) (concat (extract v_6633 0 96) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_6633 96 128) 24 8) (MInt2Float (extract v_6637 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_3292 : Mem) (v_3291 : reg (bv 128)) => do
      v_9384 <- getRegister v_3291;
      v_9388 <- evaluateAddress v_3292;
      v_9389 <- load v_9388 4;
      setRegister (lhs.of_reg v_3291) (concat (extract v_9384 0 96) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9384 96 128) 24 8) (MInt2Float v_9389 24 8)) 32));
      pure ()
    pat_end
