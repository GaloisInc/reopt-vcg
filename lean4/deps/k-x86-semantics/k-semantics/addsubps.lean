def addsubps1 : instruction :=
  definst "addsubps" $ do
    pattern fun (v_2668 : reg (bv 128)) (v_2669 : reg (bv 128)) => do
      v_4968 <- getRegister v_2669;
      v_4971 <- getRegister v_2668;
      setRegister (lhs.of_reg v_2669) (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4968 0 32) 24 8) (MInt2Float (extract v_4971 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4968 32 64) 24 8) (MInt2Float (extract v_4971 32 64) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4968 64 96) 24 8) (MInt2Float (extract v_4971 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4968 96 128) 24 8) (MInt2Float (extract v_4971 96 128) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_2663 : Mem) (v_2664 : reg (bv 128)) => do
      v_9223 <- getRegister v_2664;
      v_9226 <- evaluateAddress v_2663;
      v_9227 <- load v_9226 16;
      setRegister (lhs.of_reg v_2664) (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9223 0 32) 24 8) (MInt2Float (extract v_9227 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9223 32 64) 24 8) (MInt2Float (extract v_9227 32 64) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9223 64 96) 24 8) (MInt2Float (extract v_9227 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9223 96 128) 24 8) (MInt2Float (extract v_9227 96 128) 24 8)) 32)));
      pure ()
    pat_end
