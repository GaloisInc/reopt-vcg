def vpsllvd1 : instruction :=
  definst "vpsllvd" $ do
    pattern fun (v_3119 : reg (bv 128)) (v_3120 : reg (bv 128)) (v_3121 : reg (bv 128)) => do
      v_8176 <- getRegister v_3120;
      v_8177 <- eval (extract v_8176 0 32);
      v_8178 <- getRegister v_3119;
      v_8184 <- eval (extract v_8176 32 64);
      v_8190 <- eval (extract v_8176 64 96);
      v_8196 <- eval (extract v_8176 96 128);
      setRegister (lhs.of_reg v_3121) (concat (extract (shl v_8177 (uvalueMInt (extract v_8178 0 32))) 0 (bitwidthMInt v_8177)) (concat (extract (shl v_8184 (uvalueMInt (extract v_8178 32 64))) 0 (bitwidthMInt v_8184)) (concat (extract (shl v_8190 (uvalueMInt (extract v_8178 64 96))) 0 (bitwidthMInt v_8190)) (extract (shl v_8196 (uvalueMInt (extract v_8178 96 128))) 0 (bitwidthMInt v_8196)))));
      pure ()
    pat_end;
    pattern fun (v_3130 : reg (bv 256)) (v_3131 : reg (bv 256)) (v_3132 : reg (bv 256)) => do
      v_8211 <- getRegister v_3131;
      v_8212 <- eval (extract v_8211 0 32);
      v_8213 <- getRegister v_3130;
      v_8219 <- eval (extract v_8211 32 64);
      v_8225 <- eval (extract v_8211 64 96);
      v_8231 <- eval (extract v_8211 96 128);
      v_8237 <- eval (extract v_8211 128 160);
      v_8243 <- eval (extract v_8211 160 192);
      v_8249 <- eval (extract v_8211 192 224);
      v_8255 <- eval (extract v_8211 224 256);
      setRegister (lhs.of_reg v_3132) (concat (extract (shl v_8212 (uvalueMInt (extract v_8213 0 32))) 0 (bitwidthMInt v_8212)) (concat (extract (shl v_8219 (uvalueMInt (extract v_8213 32 64))) 0 (bitwidthMInt v_8219)) (concat (extract (shl v_8225 (uvalueMInt (extract v_8213 64 96))) 0 (bitwidthMInt v_8225)) (concat (extract (shl v_8231 (uvalueMInt (extract v_8213 96 128))) 0 (bitwidthMInt v_8231)) (concat (extract (shl v_8237 (uvalueMInt (extract v_8213 128 160))) 0 (bitwidthMInt v_8237)) (concat (extract (shl v_8243 (uvalueMInt (extract v_8213 160 192))) 0 (bitwidthMInt v_8243)) (concat (extract (shl v_8249 (uvalueMInt (extract v_8213 192 224))) 0 (bitwidthMInt v_8249)) (extract (shl v_8255 (uvalueMInt (extract v_8213 224 256))) 0 (bitwidthMInt v_8255)))))))));
      pure ()
    pat_end;
    pattern fun (v_3116 : Mem) (v_3114 : reg (bv 128)) (v_3115 : reg (bv 128)) => do
      v_15033 <- getRegister v_3114;
      v_15034 <- eval (extract v_15033 0 32);
      v_15035 <- evaluateAddress v_3116;
      v_15036 <- load v_15035 16;
      v_15042 <- eval (extract v_15033 32 64);
      v_15048 <- eval (extract v_15033 64 96);
      v_15054 <- eval (extract v_15033 96 128);
      setRegister (lhs.of_reg v_3115) (concat (extract (shl v_15034 (uvalueMInt (extract v_15036 0 32))) 0 (bitwidthMInt v_15034)) (concat (extract (shl v_15042 (uvalueMInt (extract v_15036 32 64))) 0 (bitwidthMInt v_15042)) (concat (extract (shl v_15048 (uvalueMInt (extract v_15036 64 96))) 0 (bitwidthMInt v_15048)) (extract (shl v_15054 (uvalueMInt (extract v_15036 96 128))) 0 (bitwidthMInt v_15054)))));
      pure ()
    pat_end;
    pattern fun (v_3125 : Mem) (v_3126 : reg (bv 256)) (v_3127 : reg (bv 256)) => do
      v_15064 <- getRegister v_3126;
      v_15065 <- eval (extract v_15064 0 32);
      v_15066 <- evaluateAddress v_3125;
      v_15067 <- load v_15066 32;
      v_15073 <- eval (extract v_15064 32 64);
      v_15079 <- eval (extract v_15064 64 96);
      v_15085 <- eval (extract v_15064 96 128);
      v_15091 <- eval (extract v_15064 128 160);
      v_15097 <- eval (extract v_15064 160 192);
      v_15103 <- eval (extract v_15064 192 224);
      v_15109 <- eval (extract v_15064 224 256);
      setRegister (lhs.of_reg v_3127) (concat (extract (shl v_15065 (uvalueMInt (extract v_15067 0 32))) 0 (bitwidthMInt v_15065)) (concat (extract (shl v_15073 (uvalueMInt (extract v_15067 32 64))) 0 (bitwidthMInt v_15073)) (concat (extract (shl v_15079 (uvalueMInt (extract v_15067 64 96))) 0 (bitwidthMInt v_15079)) (concat (extract (shl v_15085 (uvalueMInt (extract v_15067 96 128))) 0 (bitwidthMInt v_15085)) (concat (extract (shl v_15091 (uvalueMInt (extract v_15067 128 160))) 0 (bitwidthMInt v_15091)) (concat (extract (shl v_15097 (uvalueMInt (extract v_15067 160 192))) 0 (bitwidthMInt v_15097)) (concat (extract (shl v_15103 (uvalueMInt (extract v_15067 192 224))) 0 (bitwidthMInt v_15103)) (extract (shl v_15109 (uvalueMInt (extract v_15067 224 256))) 0 (bitwidthMInt v_15109)))))))));
      pure ()
    pat_end
