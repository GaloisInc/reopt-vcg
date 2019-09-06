def vfnmadd132ps1 : instruction :=
  definst "vfnmadd132ps" $ do
    pattern fun (v_3189 : reg (bv 128)) (v_3190 : reg (bv 128)) (v_3191 : reg (bv 128)) => do
      v_6914 <- getRegister v_3191;
      v_6916 <- getRegister v_3190;
      v_6918 <- getRegister v_3189;
      setRegister (lhs.of_reg v_3191) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_6914 0 32) (extract v_6916 0 32) (extract v_6918 0 32)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_6914 32 64) (extract v_6916 32 64) (extract v_6918 32 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_6914 64 96) (extract v_6916 64 96) (extract v_6918 64 96)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_6914 96 128) (extract v_6916 96 128) (extract v_6918 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3203 : reg (bv 256)) (v_3204 : reg (bv 256)) (v_3205 : reg (bv 256)) => do
      v_6942 <- getRegister v_3205;
      v_6944 <- getRegister v_3204;
      v_6946 <- getRegister v_3203;
      setRegister (lhs.of_reg v_3205) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_6942 0 32) (extract v_6944 0 32) (extract v_6946 0 32)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_6942 32 64) (extract v_6944 32 64) (extract v_6946 32 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_6942 64 96) (extract v_6944 64 96) (extract v_6946 64 96)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_6942 96 128) (extract v_6944 96 128) (extract v_6946 96 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_6942 128 160) (extract v_6944 128 160) (extract v_6946 128 160)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_6942 160 192) (extract v_6944 160 192) (extract v_6946 160 192)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_6942 192 224) (extract v_6944 192 224) (extract v_6946 192 224)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_6942 224 256) (extract v_6944 224 256) (extract v_6946 224 256)))))))));
      pure ()
    pat_end;
    pattern fun (v_3186 : Mem) (v_3184 : reg (bv 128)) (v_3185 : reg (bv 128)) => do
      v_12688 <- getRegister v_3185;
      v_12690 <- getRegister v_3184;
      v_12692 <- evaluateAddress v_3186;
      v_12693 <- load v_12692 16;
      setRegister (lhs.of_reg v_3185) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12688 0 32) (extract v_12690 0 32) (extract v_12693 0 32)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12688 32 64) (extract v_12690 32 64) (extract v_12693 32 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12688 64 96) (extract v_12690 64 96) (extract v_12693 64 96)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12688 96 128) (extract v_12690 96 128) (extract v_12693 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3195 : Mem) (v_3198 : reg (bv 256)) (v_3199 : reg (bv 256)) => do
      v_12712 <- getRegister v_3199;
      v_12714 <- getRegister v_3198;
      v_12716 <- evaluateAddress v_3195;
      v_12717 <- load v_12716 32;
      setRegister (lhs.of_reg v_3199) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12712 0 32) (extract v_12714 0 32) (extract v_12717 0 32)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12712 32 64) (extract v_12714 32 64) (extract v_12717 32 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12712 64 96) (extract v_12714 64 96) (extract v_12717 64 96)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12712 96 128) (extract v_12714 96 128) (extract v_12717 96 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12712 128 160) (extract v_12714 128 160) (extract v_12717 128 160)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12712 160 192) (extract v_12714 160 192) (extract v_12717 160 192)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12712 192 224) (extract v_12714 192 224) (extract v_12717 192 224)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12712 224 256) (extract v_12714 224 256) (extract v_12717 224 256)))))))));
      pure ()
    pat_end
