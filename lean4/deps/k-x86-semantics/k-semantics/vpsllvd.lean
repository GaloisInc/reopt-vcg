def vpsllvd1 : instruction :=
  definst "vpsllvd" $ do
    pattern fun (v_3131 : reg (bv 128)) (v_3132 : reg (bv 128)) (v_3133 : reg (bv 128)) => do
      v_7848 <- getRegister v_3132;
      v_7850 <- getRegister v_3131;
      setRegister (lhs.of_reg v_3133) (concat (extract (shl (extract v_7848 0 32) (uvalueMInt (extract v_7850 0 32))) 0 32) (concat (extract (shl (extract v_7848 32 64) (uvalueMInt (extract v_7850 32 64))) 0 32) (concat (extract (shl (extract v_7848 64 96) (uvalueMInt (extract v_7850 64 96))) 0 32) (extract (shl (extract v_7848 96 128) (uvalueMInt (extract v_7850 96 128))) 0 32))));
      pure ()
    pat_end;
    pattern fun (v_3143 : reg (bv 256)) (v_3144 : reg (bv 256)) (v_3145 : reg (bv 256)) => do
      v_7879 <- getRegister v_3144;
      v_7881 <- getRegister v_3143;
      setRegister (lhs.of_reg v_3145) (concat (extract (shl (extract v_7879 0 32) (uvalueMInt (extract v_7881 0 32))) 0 32) (concat (extract (shl (extract v_7879 32 64) (uvalueMInt (extract v_7881 32 64))) 0 32) (concat (extract (shl (extract v_7879 64 96) (uvalueMInt (extract v_7881 64 96))) 0 32) (concat (extract (shl (extract v_7879 96 128) (uvalueMInt (extract v_7881 96 128))) 0 32) (concat (extract (shl (extract v_7879 128 160) (uvalueMInt (extract v_7881 128 160))) 0 32) (concat (extract (shl (extract v_7879 160 192) (uvalueMInt (extract v_7881 160 192))) 0 32) (concat (extract (shl (extract v_7879 192 224) (uvalueMInt (extract v_7881 192 224))) 0 32) (extract (shl (extract v_7879 224 256) (uvalueMInt (extract v_7881 224 256))) 0 32))))))));
      pure ()
    pat_end;
    pattern fun (v_3125 : Mem) (v_3126 : reg (bv 128)) (v_3127 : reg (bv 128)) => do
      v_14235 <- getRegister v_3126;
      v_14237 <- evaluateAddress v_3125;
      v_14238 <- load v_14237 16;
      setRegister (lhs.of_reg v_3127) (concat (extract (shl (extract v_14235 0 32) (uvalueMInt (extract v_14238 0 32))) 0 32) (concat (extract (shl (extract v_14235 32 64) (uvalueMInt (extract v_14238 32 64))) 0 32) (concat (extract (shl (extract v_14235 64 96) (uvalueMInt (extract v_14238 64 96))) 0 32) (extract (shl (extract v_14235 96 128) (uvalueMInt (extract v_14238 96 128))) 0 32))));
      pure ()
    pat_end;
    pattern fun (v_3136 : Mem) (v_3138 : reg (bv 256)) (v_3139 : reg (bv 256)) => do
      v_14262 <- getRegister v_3138;
      v_14264 <- evaluateAddress v_3136;
      v_14265 <- load v_14264 32;
      setRegister (lhs.of_reg v_3139) (concat (extract (shl (extract v_14262 0 32) (uvalueMInt (extract v_14265 0 32))) 0 32) (concat (extract (shl (extract v_14262 32 64) (uvalueMInt (extract v_14265 32 64))) 0 32) (concat (extract (shl (extract v_14262 64 96) (uvalueMInt (extract v_14265 64 96))) 0 32) (concat (extract (shl (extract v_14262 96 128) (uvalueMInt (extract v_14265 96 128))) 0 32) (concat (extract (shl (extract v_14262 128 160) (uvalueMInt (extract v_14265 128 160))) 0 32) (concat (extract (shl (extract v_14262 160 192) (uvalueMInt (extract v_14265 160 192))) 0 32) (concat (extract (shl (extract v_14262 192 224) (uvalueMInt (extract v_14265 192 224))) 0 32) (extract (shl (extract v_14262 224 256) (uvalueMInt (extract v_14265 224 256))) 0 32))))))));
      pure ()
    pat_end
