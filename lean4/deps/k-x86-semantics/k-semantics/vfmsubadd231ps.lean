def vfmsubadd231ps1 : instruction :=
  definst "vfmsubadd231ps" $ do
    pattern fun (v_3145 : reg (bv 128)) (v_3146 : reg (bv 128)) (v_3147 : reg (bv 128)) => do
      v_6732 <- getRegister v_3146;
      v_6735 <- getRegister v_3145;
      v_6739 <- getRegister v_3147;
      setRegister (lhs.of_reg v_3147) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6732 0 32) 24 8) (MInt2Float (extract v_6735 0 32) 24 8)) (MInt2Float (extract v_6739 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6732 32 64) 24 8) (MInt2Float (extract v_6735 32 64) 24 8)) (MInt2Float (extract v_6739 32 64) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6732 64 96) 24 8) (MInt2Float (extract v_6735 64 96) 24 8)) (MInt2Float (extract v_6739 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6732 96 128) 24 8) (MInt2Float (extract v_6735 96 128) 24 8)) (MInt2Float (extract v_6739 96 128) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_3159 : reg (bv 256)) (v_3160 : reg (bv 256)) (v_3161 : reg (bv 256)) => do
      v_6780 <- getRegister v_3160;
      v_6783 <- getRegister v_3159;
      v_6787 <- getRegister v_3161;
      setRegister (lhs.of_reg v_3161) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6780 0 32) 24 8) (MInt2Float (extract v_6783 0 32) 24 8)) (MInt2Float (extract v_6787 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6780 32 64) 24 8) (MInt2Float (extract v_6783 32 64) 24 8)) (MInt2Float (extract v_6787 32 64) 24 8)) 32)) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6780 64 96) 24 8) (MInt2Float (extract v_6783 64 96) 24 8)) (MInt2Float (extract v_6787 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6780 96 128) 24 8) (MInt2Float (extract v_6783 96 128) 24 8)) (MInt2Float (extract v_6787 96 128) 24 8)) 32)) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6780 128 160) 24 8) (MInt2Float (extract v_6783 128 160) 24 8)) (MInt2Float (extract v_6787 128 160) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6780 160 192) 24 8) (MInt2Float (extract v_6783 160 192) 24 8)) (MInt2Float (extract v_6787 160 192) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6780 192 224) 24 8) (MInt2Float (extract v_6783 192 224) 24 8)) (MInt2Float (extract v_6787 192 224) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_6780 224 256) 24 8) (MInt2Float (extract v_6783 224 256) 24 8)) (MInt2Float (extract v_6787 224 256) 24 8)) 32)))));
      pure ()
    pat_end;
    pattern fun (v_3142 : Mem) (v_3140 : reg (bv 128)) (v_3141 : reg (bv 128)) => do
      v_12522 <- getRegister v_3140;
      v_12525 <- evaluateAddress v_3142;
      v_12526 <- load v_12525 16;
      v_12530 <- getRegister v_3141;
      setRegister (lhs.of_reg v_3141) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12522 0 32) 24 8) (MInt2Float (extract v_12526 0 32) 24 8)) (MInt2Float (extract v_12530 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12522 32 64) 24 8) (MInt2Float (extract v_12526 32 64) 24 8)) (MInt2Float (extract v_12530 32 64) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12522 64 96) 24 8) (MInt2Float (extract v_12526 64 96) 24 8)) (MInt2Float (extract v_12530 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12522 96 128) 24 8) (MInt2Float (extract v_12526 96 128) 24 8)) (MInt2Float (extract v_12530 96 128) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_3151 : Mem) (v_3154 : reg (bv 256)) (v_3155 : reg (bv 256)) => do
      v_12566 <- getRegister v_3154;
      v_12569 <- evaluateAddress v_3151;
      v_12570 <- load v_12569 32;
      v_12574 <- getRegister v_3155;
      setRegister (lhs.of_reg v_3155) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12566 0 32) 24 8) (MInt2Float (extract v_12570 0 32) 24 8)) (MInt2Float (extract v_12574 0 32) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12566 32 64) 24 8) (MInt2Float (extract v_12570 32 64) 24 8)) (MInt2Float (extract v_12574 32 64) 24 8)) 32)) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12566 64 96) 24 8) (MInt2Float (extract v_12570 64 96) 24 8)) (MInt2Float (extract v_12574 64 96) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12566 96 128) 24 8) (MInt2Float (extract v_12570 96 128) 24 8)) (MInt2Float (extract v_12574 96 128) 24 8)) 32)) (concat (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12566 128 160) 24 8) (MInt2Float (extract v_12570 128 160) 24 8)) (MInt2Float (extract v_12574 128 160) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12566 160 192) 24 8) (MInt2Float (extract v_12570 160 192) 24 8)) (MInt2Float (extract v_12574 160 192) 24 8)) 32)) (concat (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12566 192 224) 24 8) (MInt2Float (extract v_12570 192 224) 24 8)) (MInt2Float (extract v_12574 192 224) 24 8)) 32) (Float2MInt (_+Float__FLOAT (_*Float__FLOAT (MInt2Float (extract v_12566 224 256) 24 8) (MInt2Float (extract v_12570 224 256) 24 8)) (MInt2Float (extract v_12574 224 256) 24 8)) 32)))));
      pure ()
    pat_end
