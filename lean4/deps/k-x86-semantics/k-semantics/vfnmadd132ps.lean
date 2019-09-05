def vfnmadd132ps1 : instruction :=
  definst "vfnmadd132ps" $ do
    pattern fun (v_3165 : reg (bv 128)) (v_3166 : reg (bv 128)) (v_3167 : reg (bv 128)) => do
      v_6887 <- getRegister v_3167;
      v_6889 <- getRegister v_3166;
      v_6891 <- getRegister v_3165;
      setRegister (lhs.of_reg v_3167) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_6887 0 32) (extract v_6889 0 32) (extract v_6891 0 32)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_6887 32 64) (extract v_6889 32 64) (extract v_6891 32 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_6887 64 96) (extract v_6889 64 96) (extract v_6891 64 96)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_6887 96 128) (extract v_6889 96 128) (extract v_6891 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3175 : reg (bv 256)) (v_3176 : reg (bv 256)) (v_3177 : reg (bv 256)) => do
      v_6915 <- getRegister v_3177;
      v_6917 <- getRegister v_3176;
      v_6919 <- getRegister v_3175;
      setRegister (lhs.of_reg v_3177) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_6915 0 32) (extract v_6917 0 32) (extract v_6919 0 32)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_6915 32 64) (extract v_6917 32 64) (extract v_6919 32 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_6915 64 96) (extract v_6917 64 96) (extract v_6919 64 96)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_6915 96 128) (extract v_6917 96 128) (extract v_6919 96 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_6915 128 160) (extract v_6917 128 160) (extract v_6919 128 160)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_6915 160 192) (extract v_6917 160 192) (extract v_6919 160 192)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_6915 192 224) (extract v_6917 192 224) (extract v_6919 192 224)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_6915 224 256) (extract v_6917 224 256) (extract v_6919 224 256)))))))));
      pure ()
    pat_end;
    pattern fun (v_3159 : Mem) (v_3160 : reg (bv 128)) (v_3161 : reg (bv 128)) => do
      v_12661 <- getRegister v_3161;
      v_12663 <- getRegister v_3160;
      v_12665 <- evaluateAddress v_3159;
      v_12666 <- load v_12665 16;
      setRegister (lhs.of_reg v_3161) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12661 0 32) (extract v_12663 0 32) (extract v_12666 0 32)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12661 32 64) (extract v_12663 32 64) (extract v_12666 32 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12661 64 96) (extract v_12663 64 96) (extract v_12666 64 96)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12661 96 128) (extract v_12663 96 128) (extract v_12666 96 128)))));
      pure ()
    pat_end;
    pattern fun (v_3170 : Mem) (v_3171 : reg (bv 256)) (v_3172 : reg (bv 256)) => do
      v_12685 <- getRegister v_3172;
      v_12687 <- getRegister v_3171;
      v_12689 <- evaluateAddress v_3170;
      v_12690 <- load v_12689 32;
      setRegister (lhs.of_reg v_3172) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12685 0 32) (extract v_12687 0 32) (extract v_12690 0 32)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12685 32 64) (extract v_12687 32 64) (extract v_12690 32 64)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12685 64 96) (extract v_12687 64 96) (extract v_12690 64 96)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12685 96 128) (extract v_12687 96 128) (extract v_12690 96 128)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12685 128 160) (extract v_12687 128 160) (extract v_12690 128 160)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12685 160 192) (extract v_12687 160 192) (extract v_12690 160 192)) (concat (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12685 192 224) (extract v_12687 192 224) (extract v_12690 192 224)) (_(_,_,_)_MINT-WRAPPER-SYNTAX vfnmadd132_single (extract v_12685 224 256) (extract v_12687 224 256) (extract v_12690 224 256)))))))));
      pure ()
    pat_end
