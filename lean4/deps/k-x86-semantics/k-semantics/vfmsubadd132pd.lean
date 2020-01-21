def vfmsubadd132pd : instruction :=
  definst "vfmsubadd132pd" $ do
    pattern fun (mem_0 : Mem) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_2);
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 16;
      v_6 <- getRegister (lhs.of_reg xmm_1);
      setRegister (lhs.of_reg xmm_2) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_3 0 64) 53 11) (MInt2Float (extract v_5 0 64) 53 11)) (MInt2Float (extract v_6 0 64) 53 11)) 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_3 64 128) (extract v_6 64 128) (extract v_5 64 128)));
      pure ()
    pat_end;
    pattern fun (mem_0 : Mem) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_2);
      v_4 <- evaluateAddress mem_0;
      v_5 <- load v_4 32;
      v_6 <- getRegister (lhs.of_reg ymm_1);
      setRegister (lhs.of_reg ymm_2) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_3 0 64) 53 11) (MInt2Float (extract v_5 0 64) 53 11)) (MInt2Float (extract v_6 0 64) 53 11)) 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_3 64 128) (extract v_6 64 128) (extract v_5 64 128))) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_3 128 192) 53 11) (MInt2Float (extract v_5 128 192) 53 11)) (MInt2Float (extract v_6 128 192) 53 11)) 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_3 192 256) (extract v_6 192 256) (extract v_5 192 256))));
      pure ()
    pat_end;
    pattern fun (xmm_0 : reg (bv 128)) (xmm_1 : reg (bv 128)) (xmm_2 : reg (bv 128)) => do
      v_3 <- getRegister (lhs.of_reg xmm_2);
      v_4 <- getRegister (lhs.of_reg xmm_0);
      v_5 <- getRegister (lhs.of_reg xmm_1);
      setRegister (lhs.of_reg xmm_2) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_3 0 64) 53 11) (MInt2Float (extract v_4 0 64) 53 11)) (MInt2Float (extract v_5 0 64) 53 11)) 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_3 64 128) (extract v_5 64 128) (extract v_4 64 128)));
      pure ()
    pat_end;
    pattern fun (ymm_0 : reg (bv 256)) (ymm_1 : reg (bv 256)) (ymm_2 : reg (bv 256)) => do
      v_3 <- getRegister (lhs.of_reg ymm_2);
      v_4 <- getRegister (lhs.of_reg ymm_0);
      v_5 <- getRegister (lhs.of_reg ymm_1);
      setRegister (lhs.of_reg ymm_2) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_3 0 64) 53 11) (MInt2Float (extract v_4 0 64) 53 11)) (MInt2Float (extract v_5 0 64) 53 11)) 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_3 64 128) (extract v_5 64 128) (extract v_4 64 128))) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_3 128 192) 53 11) (MInt2Float (extract v_4 128 192) 53 11)) (MInt2Float (extract v_5 128 192) 53 11)) 64) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfmadd132_double (extract v_3 192 256) (extract v_5 192 256) (extract v_4 192 256))));
      pure ()
    pat_end
